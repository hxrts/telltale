import Lean.Data.Json
import Rumpsteak.Runner.Validation

/-! # Rumpsteak.Runner.Logging

File logging utilities for the verification runner.

## Overview

This module provides functions for writing verification results to log files.
Both human-readable text logs and structured JSON logs are supported.

## Main Definitions

- `writeLog` - Write results to a text log file
- `writeJsonLog` - Write results to a JSON log file
-/

namespace Rumpsteak.Runner.Logging

open Lean
open Rumpsteak.Runner.Validation

/-- Write verification results to a human-readable text log file.
    Overwrites any existing file at the path. -/
def writeLog (path : System.FilePath) (role : String) (results : List BranchResult) : IO Unit := do
  let header := s!"role={role}"
  let lines := results.map fun r =>
    s!"branch={r.name},status={if r.status then "ok" else "fail"},message={r.message},exported=[{formatActionList r.exported}],projected=[{formatActionList r.projected}]"
  IO.FS.writeFile path (String.intercalate "\n" (header :: lines) ++ "\n")

/-- Write verification results to a structured JSON log file.
    Overwrites any existing file at the path. -/
def writeJsonLog (path : System.FilePath) (role : String) (results : List BranchResult) : IO Unit := do
  let payload := Json.mkObj
    [ ("role", Json.str role)
    , ("branches", Json.arr (results.map BranchResult.toJson |>.toArray))
    ]
  IO.FS.writeFile path (payload.pretty ++ "\n")

end Rumpsteak.Runner.Logging
