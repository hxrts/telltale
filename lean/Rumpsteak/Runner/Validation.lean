import Lean.Data.Json
import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.Choreography
import Rumpsteak.Protocol.Projection
import Rumpsteak.Protocol.Program
import Rumpsteak.Protocol.Subtyping
import Rumpsteak.Runner.Json

/-! # Rumpsteak.Runner.Validation

Validation logic for comparing programs against projections.

## Overview

This module provides the core validation functions that check whether
exported programs conform to their projected local types. It evaluates
each program branch against the projection and produces detailed results.

## Main Definitions

- `BranchResult` - Result of validating a single branch
- `formatAction`, `formatActionList` - Action formatting for diagnostics
- `evaluateBranch` - Validate one branch against a projection
- `checkProgramExport` - Validate all branches of an exported program
-/

namespace Rumpsteak.Runner.Validation

open Lean
open Rumpsteak.Protocol.Core
open Rumpsteak.Protocol.Choreography
open Rumpsteak.Protocol.Projection
open Rumpsteak.Protocol.Program
open Rumpsteak.Protocol.Subtyping
open Rumpsteak.Runner.Json

/-! ## Formatting Helpers -/

/-- Format a single local action for display. -/
def formatAction (action : LocalAction) : String :=
  let kind := match action.kind with
    | LocalKind.send => "send"
    | LocalKind.recv => "recv"
  s!"{kind}-{action.partner}-{action.label}"

/-- Format a list of actions as a comma-separated string. -/
def formatActionList (actions : List LocalAction) : String :=
  String.intercalate ", " (actions.map formatAction)

/-! ## Branch Result -/

/-- Result of validating a single program branch against a projection. -/
structure BranchResult where
  /-- Branch name (or "<default>" for unnamed branches). -/
  name : String
  /-- The actions exported by the program. -/
  exported : List LocalAction
  /-- The actions from the projected local type. -/
  projected : List LocalAction
  /-- Actions in exported that don't appear in projected. -/
  missing : List LocalAction
  /-- Whether exported is a subsequence of projected. -/
  subseqOk : Bool
  /-- Whether all exported labels appear in projected. -/
  labelsOk : Bool
  /-- Overall validation status. -/
  status : Bool
  /-- Human-readable message describing the result. -/
  message : String

/-- Convert a branch result to JSON for logging. -/
def BranchResult.toJson (r : BranchResult) : Json :=
  Json.mkObj
    [ ("branch", Json.str r.name)
    , ("status", Json.str (if r.status then "ok" else "fail"))
    , ("message", Json.str r.message)
    , ("exported", Json.arr (r.exported.map (fun a => Json.str (formatAction a)) |>.toArray))
    , ("projected", Json.arr (r.projected.map (fun a => Json.str (formatAction a)) |>.toArray))
    , ("missing", Json.arr (r.missing.map (fun a => Json.str (formatAction a)) |>.toArray))
    ]

/-! ## Validation Functions -/

/-- Convert an effect to a local action (duplicated here to avoid import cycles). -/
def effectToLocalAction : Effect → LocalAction
  | .send partner label => { kind := LocalKind.send, partner := partner, label := label }
  | .recv partner label => { kind := LocalKind.recv, partner := partner, label := label }

/-- Evaluate a single branch against the projected local type.
    Checks membership, subsequence ordering, and label containment. -/
def evaluateBranch (branch : ProgramBranch) (projected : List LocalAction) : BranchResult :=
  let exported := branch.effects.map effectToLocalAction
  let missing := exported.filter (fun a => !projected.any (· == a))
  let branchLt : LocalType := { actions := exported }
  let subseqOk := isSubtype branchLt { actions := projected }
  let labelsOk := subLabelsOf branchLt { actions := projected }
  let status := missing.isEmpty && subseqOk && labelsOk
  let message :=
    if !missing.isEmpty then
      s!"missing actions: {formatActionList missing}"
    else if !subseqOk then
      s!"not a subsequence. exported=[{formatActionList exported}] projected=[{formatActionList projected}]"
    else if !labelsOk then
      let extra := exported.filter (fun a => !projected.any (·.label == a.label))
      let labels := extra.map (·.label) |>.eraseDups
      s!"unexpected labels: {String.intercalate ", " labels}"
    else
      "ok"
  { name := branch.branch.getD "<default>"
  , exported
  , projected
  , missing
  , subseqOk
  , labelsOk
  , status
  , message }

/-- Validate all branches of an exported program against the choreography projection.
    Returns an error if any branch fails, or the list of results on success. -/
def checkProgramExport (ch : Choreography) (programExport : ProgramExport) :
    Except String (List BranchResult) := do
  let role ← match ch.roles.find? (fun r => r.name == programExport.role) with
    | some r => Except.ok r
    | none => Except.error s!"Program references unknown role '{programExport.role}'"
  let localType := project ch role
  let results := programExport.programs.map (fun b => evaluateBranch b localType.actions)
  match results.find? (fun r => !r.status) with
  | some bad => Except.error s!"Branch {bad.name} failed: {bad.message}"
  | none => Except.ok results

end Rumpsteak.Runner.Validation
