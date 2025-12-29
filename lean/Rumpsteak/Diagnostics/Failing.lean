import Lean.Data.Json

/-! # Rumpsteak.Diagnostics.Failing

Failure detection utilities for negative testing.

## Overview

This module provides utilities for verifying that the runner correctly
detects and reports validation failures. It parses the JSON log from
an intentionally-failing test case and checks for expected error messages.

## Main Definitions

- `checkFailingLog` - Verify that a failure log mentions the expected error
-/

namespace Rumpsteak.Diagnostics.Failing

open Lean

/-- Check that the failing test log contains the expected "WrongLabel" error.
    This is used by the CI to verify that intentional failures are detected.

    Returns `true` if the log file exists and contains a message mentioning
    "WrongLabel", indicating the runner correctly identified the mismatch. -/
def checkFailingLog : IO Bool := do
  let path := System.FilePath.mk "lean/artifacts/runner-failing-chef.json"
  let content ← IO.FS.readFile path
  match Json.parse content with
  | Except.error _ => pure false
  | Except.ok j =>
    match j.getObjVal? "branches" with
    | Except.error _ => pure false
    | Except.ok branchesJson =>
      match branchesJson.getArr? with
      | Except.error _ => pure false
      | Except.ok arr =>
        let msgs := arr.toList.filterMap (fun b => do
          match b.getObjVal? "message" with
          | Except.error _ => none
          | Except.ok msgJson => msgJson.getStr?.toOption)
        -- Check if any message contains "WrongLabel"
        pure (msgs.any (fun m => (m.splitOn "WrongLabel").length > 1))

end Rumpsteak.Diagnostics.Failing
