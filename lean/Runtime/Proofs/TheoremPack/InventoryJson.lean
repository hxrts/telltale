import Lean.Data.Json
import Runtime.Proofs.TheoremPack.Inventory

/-! # Theorem-Pack Inventory JSON

JSON encoding of a flat theorem-pack inventory (`theoremInventory`) as an
object `{key: bool}`. This is the wire shape parsed by Rust
`LeanEvidenceInventory::from_json_str`. Flags keep the meaning documented on
`theoremInventory`: presence of a premise bundle, not a proof status. -/

set_option autoImplicit false

namespace Runtime
namespace Proofs

open Lean (Json)

universe u v

/-- Encode an inventory as a JSON object `{key: bool}`. -/
def inventoryToJson (inventory : List (String × Bool)) : Json :=
  Json.mkObj (inventory.map fun (key, flag) => (key, Json.bool flag))

/-- Check that `json` encodes exactly `inventory`: every entry is present with
its flag and the object has no extra or collapsed (duplicate) keys. -/
def inventoryJsonMatches (inventory : List (String × Bool)) (json : Json) : Bool :=
  let entriesMatch := inventory.all fun (key, flag) =>
    match json.getObjValAs? Bool key with
    | .ok decoded => decoded == flag
    | .error _ => false
  let sizeMatches :=
    match json.getObj? with
    | .ok obj => obj.size == inventory.length
    | .error _ => false
  entriesMatch && sizeMatches

/-- Pack-level JSON export of `theoremInventory`. -/
def theoremInventoryJson
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : ProtocolMachineTheoremPack (space := space)) : Json :=
  inventoryToJson (theoremInventory (space := space) pack)

#guard inventoryJsonMatches [("a", true), ("b", false)]
  (inventoryToJson [("a", true), ("b", false)])

#guard !inventoryJsonMatches [("a", true)] (inventoryToJson [("a", false)])

end Proofs
end Runtime
