-- Parses the failing JSON log to assert the runner reports the expected mismatch.
import Lean
import Rumpsteak.Runner

open Lean
open Rumpsteak

namespace Rumpsteak.DiagnosticsFailing

/-- Expect the failing log to mention WrongLabel in the message. -/
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
        pure (msgs.any (fun m => (m.splitOn "WrongLabel").length > 1))

end Rumpsteak.DiagnosticsFailing
