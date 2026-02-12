import Lean.Data.Json
import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import Choreography.Projection.Project.Primitive

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

/-- Deserialize a PayloadSort from JSON with fuel for termination. -/
def payloadSortFromJsonAux (fuel : Nat) (j : Json) : Except String PayloadSort :=
  match fuel with
  | 0 => .error "payloadSortFromJson: recursion limit exceeded"
  | fuel' + 1 =>
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
              match j.getObjValAs? (Array Json) "prod" with
              | .error e => .error e
              | .ok prodArr =>
                  if h : prodArr.size = 2 then
                    match payloadSortFromJsonAux fuel' prodArr[0], payloadSortFromJsonAux fuel' prodArr[1] with
                    | .ok l, .ok r => .ok (.prod l r)
                    | .error e, _ => .error e
                    | _, .error e => .error e
                  else .error "prod must have 2 elements"

/-- Deserialize a PayloadSort from JSON. -/
def payloadSortFromJson (j : Json) : Except String PayloadSort :=
  payloadSortFromJsonAux (j.compress.length + 1) j

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

/-! ## GlobalType Encoding -/

/-- Serialize a GlobalType to JSON. -/
def globalTypeToJson : GlobalType → Json
  | .end => Json.mkObj [("kind", "end")]
  | .comm sender receiver branches =>
      -- Serialize each branch as {label, continuation}.
      let branchesJson := branches.attach.map fun ⟨(label, cont), hmem⟩ =>
        have : sizeOf cont < sizeOf branches := by
          have h1 : sizeOf cont < sizeOf (label, cont) := by simp; omega
          have h2 := List.sizeOf_lt_of_mem hmem
          omega
        Json.mkObj [("label", labelToJson label), ("continuation", globalTypeToJson cont)]
      Json.mkObj [("kind", "comm"), ("sender", Json.str sender),
        ("receiver", Json.str receiver), ("branches", Json.arr branchesJson.toArray)]
  | .mu var body =>
      Json.mkObj [("kind", "rec"), ("var", Json.str var), ("body", globalTypeToJson body)]
  | .var name =>
      Json.mkObj [("kind", "var"), ("name", Json.str name)]
  | .delegate delegator delegatee sessionId role cont =>
      Json.mkObj [("kind", "delegate"), ("delegator", Json.str delegator),
        ("delegatee", Json.str delegatee), ("session_id", Json.num sessionId),
        ("role", Json.str role), ("continuation", globalTypeToJson cont)]
termination_by g => sizeOf g

/-! ## GlobalType Decoding -/

/-- Deserialize a GlobalType from JSON with fuel for termination. -/
def globalTypeFromJsonAux (fuel : Nat) (j : Json) : Except String GlobalType :=
  match fuel with
  | 0 => .error "globalTypeFromJson: recursion limit exceeded"
  | fuel' + 1 => do
      let kind ← j.getObjValAs? String "kind"
      match kind with
      | "end" => .ok .end
      | "comm" =>
          let sender ← j.getObjValAs? String "sender"
          let receiver ← j.getObjValAs? String "receiver"
          let branchesArr ← j.getObjValAs? (Array Json) "branches"
          let branches ← branchesArr.toList.mapM fun b => do
            let label ← labelFromJson (b.getObjValD "label")
            let cont ← globalTypeFromJsonAux fuel' (b.getObjValD "continuation")
            .ok (label, cont)
          .ok (.comm sender receiver branches)
      | "rec" =>
          let var ← j.getObjValAs? String "var"
          let body ← globalTypeFromJsonAux fuel' (j.getObjValD "body")
          .ok (.mu var body)
      | "var" =>
          let name ← j.getObjValAs? String "name"
          .ok (.var name)
      | "delegate" =>
          let delegator ← j.getObjValAs? String "delegator"
          let delegatee ← j.getObjValAs? String "delegatee"
          let sessionId ← j.getObjValAs? Nat "session_id"
          let role ← j.getObjValAs? String "role"
          let cont ← globalTypeFromJsonAux fuel' (j.getObjValD "continuation")
          .ok (.delegate delegator delegatee sessionId role cont)
      | other => .error s!"invalid GlobalType kind: {other}"

/-- Deserialize a GlobalType from JSON. -/
def globalTypeFromJson (j : Json) : Except String GlobalType :=
  globalTypeFromJsonAux (j.compress.length + 1) j

/-! ## LocalTypeR Serialization -/

/-! ## LocalTypeR Encoding -/

/-- Serialize a LocalTypeR to JSON. -/
def localTypeRToJson : LocalTypeR → Json
  | .end => Json.mkObj [("kind", "end")]
  | .send partner branches =>
      let branchesJson := branches.attach.map fun ⟨(label, _vt, cont), hmem⟩ =>
        have : sizeOf cont < sizeOf branches := by
          have h1 : sizeOf cont < sizeOf (label, _vt, cont) := by simp; omega
          have h2 := List.sizeOf_lt_of_mem hmem
          omega
        Json.mkObj [("label", labelToJson label), ("continuation", localTypeRToJson cont)]
      Json.mkObj [("kind", "send"), ("partner", Json.str partner),
        ("branches", Json.arr branchesJson.toArray)]
  | .recv partner branches =>
      let branchesJson := branches.attach.map fun ⟨(label, _vt, cont), hmem⟩ =>
        have : sizeOf cont < sizeOf branches := by
          have h1 : sizeOf cont < sizeOf (label, _vt, cont) := by simp; omega
          have h2 := List.sizeOf_lt_of_mem hmem
          omega
        Json.mkObj [("label", labelToJson label), ("continuation", localTypeRToJson cont)]
      Json.mkObj [("kind", "recv"), ("partner", Json.str partner),
        ("branches", Json.arr branchesJson.toArray)]
  | .mu var body =>
      Json.mkObj [("kind", "rec"), ("var", Json.str var), ("body", localTypeRToJson body)]
  | .var name =>
      Json.mkObj [("kind", "var"), ("name", Json.str name)]
termination_by lt => sizeOf lt

/-! ## LocalTypeR Decoding -/

/-- Deserialize a LocalTypeR from JSON with fuel for termination. -/
def localTypeRFromJsonAux (fuel : Nat) (j : Json) : Except String LocalTypeR :=
  match fuel with
  | 0 => .error "localTypeRFromJson: recursion limit exceeded"
  | fuel' + 1 => do
      let kind ← j.getObjValAs? String "kind"
      match kind with
      | "end" => .ok .end
      | "send" =>
          let partner ← j.getObjValAs? String "partner"
          let branchesArr ← j.getObjValAs? (Array Json) "branches"
          let branches ← branchesArr.toList.mapM fun b => do
            let label ← labelFromJson (b.getObjValD "label")
            let cont ← localTypeRFromJsonAux fuel' (b.getObjValD "continuation")
            .ok (label, none, cont)
          .ok (.send partner branches)
      | "recv" =>
          let partner ← j.getObjValAs? String "partner"
          let branchesArr ← j.getObjValAs? (Array Json) "branches"
          let branches ← branchesArr.toList.mapM fun b => do
            let label ← labelFromJson (b.getObjValD "label")
            let cont ← localTypeRFromJsonAux fuel' (b.getObjValD "continuation")
            .ok (label, none, cont)
          .ok (.recv partner branches)
      | "rec" =>
          let var ← j.getObjValAs? String "var"
          let body ← localTypeRFromJsonAux fuel' (j.getObjValD "body")
          .ok (.mu var body)
      | "var" =>
          let name ← j.getObjValAs? String "name"
          .ok (.var name)
      | other => .error s!"invalid LocalTypeR kind: {other}"

/-- Deserialize a LocalTypeR from JSON. -/
def localTypeRFromJson (j : Json) : Except String LocalTypeR :=
  localTypeRFromJsonAux (j.compress.length + 1) j

end Choreography.Projection.Json
