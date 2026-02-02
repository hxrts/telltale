import Lean.Data.Json
import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import Choreography.Projection.Trans

/-
The Problem. Serialize GlobalType and LocalTypeR to/from JSON for the Lean-Rust
bridge. The JSON schema matches the Rust lean-bridge crate (export.rs/import.rs):

  GlobalType: {"kind": "end"}, {"kind": "comm", ...}, {"kind": "rec", ...}, {"kind": "var", ...}
  LocalTypeR: {"kind": "end"}, {"kind": "send", ...}, {"kind": "recv", ...}, {"kind": "rec", ...}, {"kind": "var", ...}
  PayloadSort: "unit", "nat", "bool", "string", "real", {"vector": n}, {"prod": [left, right]}
  Label: {"name": "...", "sort": <sort>}

Solution Structure. Mutual recursion for GlobalType/LocalTypeR branches,
matching the Rust lean-bridge JSON format exactly.
-/

/-! # Choreography.Projection.Json

JSON serialization for GlobalType, LocalTypeR, PayloadSort, and Label.
Matches the lean-bridge JSON schema used by Rust export/import.

## Expose

- `payloadSortToJson` / `payloadSortFromJson`
- `labelToJson` / `labelFromJson`
- `globalTypeToJson` / `globalTypeFromJson`
- `localTypeRToJson` / `localTypeRFromJson`
-/

set_option autoImplicit false

namespace Choreography.Projection.Json

open Lean (Json ToJson FromJson)
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-! ## PayloadSort Serialization -/

/-- Serialize a PayloadSort to JSON. -/
def payloadSortToJson : PayloadSort → Json
  | .unit => Json.str "unit"
  | .nat => Json.str "nat"
  | .bool => Json.str "bool"
  | .string => Json.str "string"
  | .real => Json.str "real"
  | .vector n => Json.mkObj [("vector", Json.num n)]
  | .prod l r => Json.mkObj [("prod", Json.arr #[payloadSortToJson l, payloadSortToJson r])]

/-- Deserialize a PayloadSort from JSON. -/
partial def payloadSortFromJson (j : Json) : Except String PayloadSort := do
  -- Handle string sorts first, then object sorts.
  match j with
  | Json.str "unit" => .ok .unit
  | Json.str "nat" => .ok .nat
  | Json.str "bool" => .ok .bool
  | Json.str "string" => .ok .string
  | Json.str "real" => .ok .real
  | Json.str other => .error s!"invalid sort: {other}"
  | _ =>
      -- Try object-shaped sorts: {"vector": n} or {"prod": [l, r]}.
      let vectorResult := j.getObjValAs? Nat "vector"
      match vectorResult with
      | .ok n => .ok (.vector n)
      | .error _ =>
          let prodArr ← j.getObjValAs? (Array Json) "prod"
          if prodArr.size == 2 then do
            let l ← payloadSortFromJson prodArr[0]!
            let r ← payloadSortFromJson prodArr[1]!
            .ok (.prod l r)
          else .error "prod must have 2 elements"

/-! ## Label Serialization -/

/-- Serialize a Label to JSON. -/
def labelToJson (l : Label) : Json :=
  Json.mkObj [("name", Json.str l.name), ("sort", payloadSortToJson l.sort)]

/-- Deserialize a Label from JSON. -/
def labelFromJson (j : Json) : Except String Label := do
  let name ← j.getObjValAs? String "name"
  let sortJson := j.getObjValD "sort"
  let sort ← payloadSortFromJson sortJson
  .ok { name := name, sort := sort }

/-! ## GlobalType Serialization -/

/-- Serialize a GlobalType to JSON. -/
partial def globalTypeToJson : GlobalType → Json
  | .end => Json.mkObj [("kind", "end")]
  | .comm sender receiver branches =>
      -- Serialize each branch as {label, continuation}.
      let branchesJson := branches.map fun (label, cont) =>
        Json.mkObj [("label", labelToJson label), ("continuation", globalTypeToJson cont)]
      Json.mkObj [("kind", "comm"), ("sender", Json.str sender),
        ("receiver", Json.str receiver), ("branches", Json.arr branchesJson.toArray)]
  | .mu var body =>
      Json.mkObj [("kind", "rec"), ("var", Json.str var), ("body", globalTypeToJson body)]
  | .var name =>
      Json.mkObj [("kind", "var"), ("name", Json.str name)]

/-- Deserialize a GlobalType from JSON. -/
partial def globalTypeFromJson (j : Json) : Except String GlobalType := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "end" => .ok .end
  | "comm" =>
      let sender ← j.getObjValAs? String "sender"
      let receiver ← j.getObjValAs? String "receiver"
      let branchesArr ← j.getObjValAs? (Array Json) "branches"
      let branches ← branchesArr.toList.mapM fun b => do
        let label ← labelFromJson (b.getObjValD "label")
        let cont ← globalTypeFromJson (b.getObjValD "continuation")
        .ok (label, cont)
      .ok (.comm sender receiver branches)
  | "rec" =>
      let var ← j.getObjValAs? String "var"
      let body ← globalTypeFromJson (j.getObjValD "body")
      .ok (.mu var body)
  | "var" =>
      let name ← j.getObjValAs? String "name"
      .ok (.var name)
  | other => .error s!"invalid GlobalType kind: {other}"

/-! ## LocalTypeR Serialization -/

/-- Serialize a LocalTypeR to JSON. -/
partial def localTypeRToJson : LocalTypeR → Json
  | .end => Json.mkObj [("kind", "end")]
  | .send partner branches =>
      let branchesJson := branches.map fun (label, _vt, cont) =>
        Json.mkObj [("label", labelToJson label), ("continuation", localTypeRToJson cont)]
      Json.mkObj [("kind", "send"), ("partner", Json.str partner),
        ("branches", Json.arr branchesJson.toArray)]
  | .recv partner branches =>
      let branchesJson := branches.map fun (label, _vt, cont) =>
        Json.mkObj [("label", labelToJson label), ("continuation", localTypeRToJson cont)]
      Json.mkObj [("kind", "recv"), ("partner", Json.str partner),
        ("branches", Json.arr branchesJson.toArray)]
  | .mu var body =>
      Json.mkObj [("kind", "rec"), ("var", Json.str var), ("body", localTypeRToJson body)]
  | .var name =>
      Json.mkObj [("kind", "var"), ("name", Json.str name)]

/-- Deserialize a LocalTypeR from JSON. -/
partial def localTypeRFromJson (j : Json) : Except String LocalTypeR := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "end" => .ok .end
  | "send" =>
      let partner ← j.getObjValAs? String "partner"
      let branchesArr ← j.getObjValAs? (Array Json) "branches"
      let branches ← branchesArr.toList.mapM fun b => do
        let label ← labelFromJson (b.getObjValD "label")
        let cont ← localTypeRFromJson (b.getObjValD "continuation")
        .ok (label, none, cont)
      .ok (.send partner branches)
  | "recv" =>
      let partner ← j.getObjValAs? String "partner"
      let branchesArr ← j.getObjValAs? (Array Json) "branches"
      let branches ← branchesArr.toList.mapM fun b => do
        let label ← labelFromJson (b.getObjValD "label")
        let cont ← localTypeRFromJson (b.getObjValD "continuation")
        .ok (label, none, cont)
      .ok (.recv partner branches)
  | "rec" =>
      let var ← j.getObjValAs? String "var"
      let body ← localTypeRFromJson (j.getObjValD "body")
      .ok (.mu var body)
  | "var" =>
      let name ← j.getObjValAs? String "name"
      .ok (.var name)
  | other => .error s!"invalid LocalTypeR kind: {other}"

end Choreography.Projection.Json
