import Rumpsteak.Runner.Json
import Rumpsteak.Runner.Validation
import Rumpsteak.Runner.Logging

/-! # Rumpsteak.Runner.Main

CLI entry point for the verification runner.

## Overview

This module provides the main function and command-line argument parsing
for the `rumpsteak_runner` executable. It orchestrates JSON file loading,
validation, and result logging.

## Usage

```
rumpsteak_runner --choreography <path> --program <path> [--log <path>] [--json-log <path>]
```

## Main Definitions

- `runPaths` - Core orchestration function
- `runnerMain` - CLI argument parser and dispatcher
- `main` - Entry point
-/

namespace Rumpsteak.Runner.Main

open Rumpsteak.Runner.Json
open Rumpsteak.Runner.Validation
open Rumpsteak.Runner.Logging

/-- Run validation given file paths for choreography and program JSON.
    Optionally writes results to text and/or JSON log files.
    Returns 0 on success, 1 on any error. -/
def runPaths (chPath progPath : System.FilePath)
    (logPath : Option System.FilePath := none)
    (jsonLog : Option System.FilePath := none) : IO UInt32 := do
  -- Load and parse choreography
  let choreoJson ← readJsonFile chPath
  match choreoJson with
  | Except.error err =>
    IO.eprintln s!"Failed to parse choreography JSON: {err}"
    pure (1 : UInt32)
  | Except.ok choreoDoc =>
    match parseChoreography choreoDoc with
    | Except.error err =>
      IO.eprintln s!"Failed to decode choreography: {err}"
      pure (1 : UInt32)
    | Except.ok choreography =>
      -- Load and parse program
      let programJson ← readJsonFile progPath
      match programJson with
      | Except.error err =>
        IO.eprintln s!"Failed to parse program JSON: {err}"
        pure (1 : UInt32)
      | Except.ok programDoc =>
        match parseProgramExport programDoc with
        | Except.error err =>
          IO.eprintln s!"Failed to decode program: {err}"
          pure (1 : UInt32)
        | Except.ok programExport =>
          -- Validate
          match checkProgramExport choreography programExport with
          | Except.error err =>
            IO.eprintln err
            pure (1 : UInt32)
          | Except.ok results =>
            -- Write logs if requested
            match logPath with
            | some path => writeLog path programExport.role results
            | none => pure ()
            match jsonLog with
            | some path => writeJsonLog path programExport.role results
            | none => pure ()
            IO.println s!"Lean runner: choreography and program validated for {programExport.role}"
            pure (0 : UInt32)

/-- Usage message for the CLI. -/
def usage : String :=
  "usage: rumpsteak_runner --choreography <path> --program <path> [--log <path>] [--json-log <path>]"

/-- Parse command-line arguments and dispatch to runPaths.
    Supports various orderings of optional --log and --json-log flags. -/
def runnerMain (args : List String) : IO UInt32 :=
  match args with
  | ["--choreography", chPath, "--program", progPath] =>
      runPaths ⟨chPath⟩ ⟨progPath⟩ none none
  | ["--choreography", chPath, "--program", progPath, "--log", logPath] =>
      runPaths ⟨chPath⟩ ⟨progPath⟩ (some ⟨logPath⟩) none
  | ["--choreography", chPath, "--program", progPath, "--json-log", jsonLog] =>
      runPaths ⟨chPath⟩ ⟨progPath⟩ none (some ⟨jsonLog⟩)
  | ["--choreography", chPath, "--program", progPath, "--log", logPath, "--json-log", jsonLog] =>
      runPaths ⟨chPath⟩ ⟨progPath⟩ (some ⟨logPath⟩) (some ⟨jsonLog⟩)
  | ["--choreography", chPath, "--program", progPath, "--json-log", jsonLog, "--log", logPath] =>
      runPaths ⟨chPath⟩ ⟨progPath⟩ (some ⟨logPath⟩) (some ⟨jsonLog⟩)
  | _ =>
    IO.println usage *> pure (1 : UInt32)

end Rumpsteak.Runner.Main

/-- Entry point for the rumpsteak_runner executable. -/
def main (args : List String) : IO UInt32 :=
  Rumpsteak.Runner.Main.runnerMain args
