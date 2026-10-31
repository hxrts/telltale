import Lean.Data.Json
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Model.CompileLocalTypeR
import Runtime.ProtocolMachine.Model.Program
import Choreography.Projection.Json

/-! # Compile LocalTypeR Export

Reads `{"local_types": [[role, localTypeR], ...]}` from stdin, compiles each role with
`compileLocalTypeR`, builds the multi-role image with `CodeImage.fromLocalTypes`, and
prints both as JSON. Used by the Rust refinement parity test
(`rust/machine/tests/compile_refinement_lean.rs`).

Instruction encoding (normalized, shared with the Rust test):
`["send", chan, val]`, `["receive", chan, dst]`, `["offer", chan, label]`,
`["choose", chan, [[label, pc], ...]]`, `["jump", pc]`, `["halt"]`, `["invoke"]`.
Any other instruction is encoded as `["unsupported"]`.
-/

set_option autoImplicit false

open Lean (Json)
open Choreography.Projection.Json

/-- Encode a compiler-emitted instruction as normalized JSON. -/
def instrToCompileJson : Instr UnitGuard UnitEffect → Json
  | .send chan val => Json.arr #["send", Json.num chan, Json.num val]
  | .receive chan dst => Json.arr #["receive", Json.num chan, Json.num dst]
  | .offer chan label => Json.arr #["offer", Json.num chan, Json.str label]
  | .choose chan table =>
      Json.arr #["choose", Json.num chan,
        Json.arr (table.map (fun (l, pc) => Json.arr #[Json.str l, Json.num pc])).toArray]
  | .jump target => Json.arr #["jump", Json.num target]
  | .halt => Json.arr #["halt"]
  | .invoke _ => Json.arr #["invoke"]
  | _ => Json.arr #["unsupported"]

/-- Encode an instruction list. -/
def codeToJson (code : List (Instr UnitGuard UnitEffect)) : Json :=
  Json.arr (code.map instrToCompileJson).toArray

/-- Parse the `[[role, localTypeR], ...]` input array. -/
def parseLocalTypes (j : Json) : Except String (List (Role × SessionTypes.LocalTypeR.LocalTypeR)) := do
  let entries ← j.getObjValAs? (Array Json) "local_types"
  entries.toList.mapM fun entry => do
    match (← entry.getArr?).toList with
    | [role, lt] => pure ((← role.getStr?), (← localTypeRFromJson lt))
    | _ => throw "invalid local_types entry"

/-- Compile per role and as a multi-role image. -/
def compileExport (locals : List (Role × SessionTypes.LocalTypeR.LocalTypeR)) : Json :=
  let programs := locals.map fun (r, lt) =>
    Json.arr #[Json.str r, codeToJson (compileLocalTypeR (γ:=UnitGuard) (ε:=UnitEffect) lt)]
  let image := CodeImage.fromLocalTypes (γ:=UnitGuard) (ε:=UnitEffect) locals .end
  let entries := image.program.entryPoints.map fun (r, pc) => Json.arr #[Json.str r, Json.num pc]
  Json.mkObj
    [ ("programs", Json.arr programs.toArray)
    , ("image_code", codeToJson image.program.code.toList)
    , ("image_entry_points", Json.arr entries.toArray) ]

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= parseLocalTypes with
  | .error e =>
      IO.eprintln s!"compile_local_type_export: {e}"
      return 1
  | .ok locals =>
      IO.println (compileExport locals).compress
      return 0
