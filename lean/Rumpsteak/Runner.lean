-- CLI runner that parses exported JSON and checks it against projections.
import Lean.Data.Json
import Rumpsteak.Choreography
import Rumpsteak.Projection
import Rumpsteak.Program
import Rumpsteak.Subtyping
import Rumpsteak.Diagnostics

/-! Minimal runner that checks each exported branch sequence against the projected
    local type. No metadata yet; goal is a stable baseline. -/

namespace Rumpsteak

open Lean
open Rumpsteak.Program (Program Effect)
open Rumpsteak.Projection
open Rumpsteak.Subtyping (isSubtype)

structure ProgramBranch where
  branch : Option String
  effects : List Effect

structure ProgramExport where
  role : String
  programs : List ProgramBranch

/-- Helpers to display actions for debugging. -/
def effectToLocalAction : Effect → LocalAction
  | .send partner label => { kind := LocalKind.send, partner := partner, label := label }
  | .recv partner label => { kind := LocalKind.recv, partner := partner, label := label }

def formatAction (action : LocalAction) : String :=
  let kind := match action.kind with
    | LocalKind.send => "send"
    | LocalKind.recv => "recv"
  s!"{kind}-{action.partner}-{action.label}"

def formatActionList (actions : List LocalAction) : String :=
  String.intercalate ", " (actions.map formatAction)

structure BranchResult where
  name : String
  exported : List LocalAction
  projected : List LocalAction
  missing : List LocalAction
  subseqOk : Bool
  labelsOk : Bool
  status : Bool
  message : String

def BranchResult.toJson (r : BranchResult) : Json :=
  Json.mkObj
    [ ("branch", Json.str r.name)
    , ("status", Json.str (if r.status then "ok" else "fail"))
    , ("message", Json.str r.message)
    , ("exported", Json.arr (r.exported.map (fun a => Json.str (formatAction a)) |>.toArray))
    , ("projected", Json.arr (r.projected.map (fun a => Json.str (formatAction a)) |>.toArray))
    , ("missing", Json.arr (r.missing.map (fun a => Json.str (formatAction a)) |>.toArray))
    ]

/-- Parse helpers -/
def getField (json : Json) (key : String) : Except String Json :=
  match json.getObjVal? key with
  | Except.ok v => Except.ok v
  | Except.error _ => Except.error s!"Missing field '{key}'"

def parseArray (json : Json) : Except String (Array Json) :=
  match json.getArr? with
  | Except.ok arr => Except.ok arr
  | Except.error _ => Except.error "Expected JSON array"

def parseString (json : Json) : Except String String :=
  match json.getStr? with
  | Except.ok s => Except.ok s
  | Except.error _ => Except.error "Expected JSON string"

/-- Choreography parsing -/
def parseRoles (json : Json) : Except String (List Role) := do
  let arr ← getField json "roles" >>= parseArray
  arr.toList.mapM (fun j => do
    let name ← parseString j
    pure { name := name })

def parseAction (json : Json) : Except String Action := do
  let origin ← getField json "from" >>= parseString
  let dest ← getField json "to" >>= parseString
  let label ← getField json "label" >>= parseString
  pure (origin, dest, label)

def parseActions (json : Json) : Except String (List Action) := do
  let arr ← getField json "actions" >>= parseArray
  arr.toList.mapM parseAction

def parseChoreography (json : Json) : Except String Choreography := do
  let roles ← parseRoles json
  let actions ← parseActions json
  pure { roles := roles, actions := actions }

/-- Program parsing -/
def parseEffect (json : Json) : Except String Effect := do
  let kind ← getField json "kind" >>= parseString
  let partner ← getField json "partner" >>= parseString
  let label ← getField json "label" >>= parseString
  match kind with
  | "send" => Except.ok (.send partner label)
  | "recv" => Except.ok (.recv partner label)
  | _ => Except.error s!"Unknown effect kind '{kind}'"

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

def parseProgramExport (json : Json) : Except String ProgramExport := do
  let role ← getField json "role" >>= parseString
  let branchesArr ← getField json "programs" >>= parseArray
  let programs ← branchesArr.toList.mapM parseBranch
  pure { role, programs }

/-- IO helper -/
def readJsonFile (path : System.FilePath) : IO (Except String Json) := do
  let content ← IO.FS.readFile path
  pure (Json.parse content)

/-- Validation -/
def evaluateBranch (branch : ProgramBranch) (projected : List LocalAction) : BranchResult :=
  let exported := branch.effects.map effectToLocalAction
  let missing := exported.filter (fun a => !projected.any (· == a))
  let branchLt : LocalType := { actions := exported }
  let subseqOk := isSubtype branchLt { actions := projected }
  let labelsOk := Rumpsteak.Projection.subLabelsOf branchLt { actions := projected }
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
  { name := branch.branch.getD "<default>", exported, projected, missing, subseqOk, labelsOk, status, message }

def checkProgramExport (ch : Choreography) (program_export : ProgramExport) : Except String (List BranchResult) := do
  let role ← match ch.roles.find? (fun r => r.name == program_export.role) with
    | some r => Except.ok r
    | none => Except.error s!"Program references unknown role '{program_export.role}'"
  let localType := project ch role
  let results := program_export.programs.map (fun b => evaluateBranch b localType.actions)
  match results.find? (fun r => !r.status) with
  | some bad => Except.error s!"Branch {bad.name} failed: {bad.message}"
  | none => Except.ok results

/-- Optional text log sink. Overwrites the file each run. -/
def writeLog (path : System.FilePath) (role : String) (results : List BranchResult) : IO Unit := do
  let header := s!"role={role}"
  let lines := results.map fun r =>
    s!"branch={r.name},status={if r.status then "ok" else "fail"},message={r.message},exported=[{formatActionList r.exported}],projected=[{formatActionList r.projected}]"
  IO.FS.writeFile path (String.intercalate "\n" (header :: lines) ++ "\n")

/-- Optional JSON log sink. Overwrites the file each run. -/
def writeJsonLog (path : System.FilePath) (role : String) (results : List BranchResult) : IO Unit := do
  let payload := Json.mkObj
    [ ("role", Json.str role)
    , ("branches", Json.arr (results.map BranchResult.toJson |>.toArray))
    ]
  IO.FS.writeFile path (payload.pretty ++ "\n")

/-- Runner orchestration -/
def runPaths (chPath progPath : System.FilePath) (logPath : Option System.FilePath := none) (jsonLog : Option System.FilePath := none) : IO UInt32 := do
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
        | Except.ok program_export =>
          match checkProgramExport choreography program_export with
          | Except.error err =>
            IO.eprintln err
            pure (1 : UInt32)
          | Except.ok results =>
            match logPath with
            | some path => writeLog path program_export.role results
            | none => pure ()
            match jsonLog with
            | some path => writeJsonLog path program_export.role results
            | none => pure ()
            IO.println s!"Lean runner: choreography and program validated for {program_export.role}"
            pure (0 : UInt32)

def usage : String :=
  "usage: rumpsteak_runner --choreography <path> --program <path> [--log <path>] [--json-log <path>]"

def runnerMain (args : List String) : IO UInt32 :=
  match args with
  | ["--choreography", chPath, "--program", progPath] => runPaths ⟨chPath⟩ ⟨progPath⟩ none none
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

end Rumpsteak

def main (args : List String) : IO UInt32 :=
  Rumpsteak.runnerMain args
