import Lean.Data.Json
import Runtime.Resources.HeapModel
import Runtime.Proofs.Heap

/-! # Runtime.Tests.HeapParityRunner

Executable heap parity runner. It reads the published heap parity fixture,
recomputes canonical bytes, tagged preimages, deterministic ordering, and
proof-path structure in Lean, and prints a JSON payload for Rust-side
comparison.
-/

set_option autoImplicit false

namespace Runtime.Tests.HeapParityRunner

open Lean (Json)
open Runtime.Resources.HeapModel

structure ResourceFixture where
  kind : String
  source : String
  dest : String
  label : String
  payload : List UInt8
  seqNo : Nat
  allocationCounter : Nat
  resourceIdDigestHex : String
  resourceLeafHex : String
  nullifierLeafHex : String
  deriving Repr, Inhabited

inductive HeapFixtureOp where
  | allocChannel (sender receiver digestHex : String)
  | allocMessage (source dest label : String) (payload : List UInt8) (seqNo : Nat) (digestHex : String)
  | allocSession (role : String) (typeHash : Nat) (digestHex : String)
  | consume (rid : ResourceId)
  deriving Repr, Inhabited

structure HeapFixture where
  operations : List HeapFixtureOp
  activeResourceIdsHex : List String
  consumedResourceIdsHex : List String
  resourceLevelsHex : List (List String)
  nullifierLevelsHex : List (List String)
  proofIndex : Nat
  proofRootHex : String
  resourceRootHex : String
  nullifierRootHex : String
  commitmentHashHex : String
  deriving Repr, Inhabited

structure ChannelFixture where
  resourceIdDigestHex : String
  deriving Repr, Inhabited

structure HeapParityFixture where
  schemaVersion : String
  hasher : String
  resourceFixture : ResourceFixture
  channelFixture : ChannelFixture
  heapFixture : HeapFixture
  deriving Repr, Inhabited

def jsonArrayStrings? (value : Json) : Except String (List String) :=
  match value with
  | .arr arr => arr.toList.mapM Json.getStr?
  | _ => .error "expected JSON array of strings"

def jsonArrayArraysStrings? (value : Json) : Except String (List (List String)) :=
  match value with
  | .arr arr => arr.toList.mapM jsonArrayStrings?
  | _ => .error "expected JSON array of string arrays"

def parseResourceId (value : Json) : Except String ResourceId := do
  .ok
    { digestHex := ← value.getObjValAs? String "digest_hex"
    , counter := ← value.getObjValAs? Nat "counter" }

def parseHeapFixtureOp (value : Json) : Except String HeapFixtureOp := do
  let kind ← value.getObjValAs? String "kind"
  match kind with
  | "alloc_channel" =>
      .ok <|
        .allocChannel
          (← value.getObjValAs? String "sender")
          (← value.getObjValAs? String "receiver")
          (← value.getObjValAs? String "resource_id_digest_hex")
  | "alloc_message" =>
      let payloadHex ← value.getObjValAs? String "payload_hex"
      let payload ←
        match bytesOfHex? payloadHex with
        | some bytes => pure bytes
        | none => .error s!"invalid payload hex: {payloadHex}"
      .ok <|
        .allocMessage
          (← value.getObjValAs? String "source")
          (← value.getObjValAs? String "dest")
          (← value.getObjValAs? String "label")
          payload
          (← value.getObjValAs? Nat "seq_no")
          (← value.getObjValAs? String "resource_id_digest_hex")
  | "alloc_session" =>
      .ok <|
        .allocSession
          (← value.getObjValAs? String "role")
          (← value.getObjValAs? Nat "type_hash")
          (← value.getObjValAs? String "resource_id_digest_hex")
  | "consume" =>
      let ridJson := value.getObjValD "resource_id"
      .ok <| .consume (← parseResourceId ridJson)
  | other =>
      .error s!"unsupported heap op kind: {other}"

def parseResourceFixture (value : Json) : Except String ResourceFixture := do
  let payloadHex ← value.getObjValAs? String "payload_hex"
  let payload ←
    match bytesOfHex? payloadHex with
    | some bytes => pure bytes
    | none => .error s!"invalid payload hex: {payloadHex}"
  .ok
    { kind := ← value.getObjValAs? String "kind"
    , source := ← value.getObjValAs? String "source"
    , dest := ← value.getObjValAs? String "dest"
    , label := ← value.getObjValAs? String "label"
    , payload := payload
    , seqNo := ← value.getObjValAs? Nat "seq_no"
    , allocationCounter := ← value.getObjValAs? Nat "allocation_counter"
    , resourceIdDigestHex := ← value.getObjValAs? String "resource_id_digest_hex"
    , resourceLeafHex := ← value.getObjValAs? String "resource_leaf_hex"
    , nullifierLeafHex := ← value.getObjValAs? String "nullifier_leaf_hex" }

def parseHeapFixture (value : Json) : Except String HeapFixture := do
  let operationsJson ← value.getObjValAs? (Array Json) "operations"
  .ok
    { operations := ← operationsJson.toList.mapM parseHeapFixtureOp
    , activeResourceIdsHex := ← jsonArrayStrings? (value.getObjValD "active_resource_ids_hex")
    , consumedResourceIdsHex := ← jsonArrayStrings? (value.getObjValD "consumed_resource_ids_hex")
    , resourceLevelsHex := ← jsonArrayArraysStrings? (value.getObjValD "resource_levels_hex")
    , nullifierLevelsHex := ← jsonArrayArraysStrings? (value.getObjValD "nullifier_levels_hex")
    , proofIndex := ← value.getObjValAs? Nat "proof_index"
    , proofRootHex := ← value.getObjValAs? String "proof_root_hex"
    , resourceRootHex := ← value.getObjValAs? String "resource_root_hex"
    , nullifierRootHex := ← value.getObjValAs? String "nullifier_root_hex"
    , commitmentHashHex := ← value.getObjValAs? String "commitment_hash_hex" }

def parseFixture (value : Json) : Except String HeapParityFixture := do
  .ok
    { schemaVersion := ← value.getObjValAs? String "schema_version"
    , hasher := ← value.getObjValAs? String "hasher"
    , resourceFixture := ← parseResourceFixture (value.getObjValD "resource_fixture")
    , channelFixture :=
        { resourceIdDigestHex :=
            ← (value.getObjValD "channel_fixture").getObjValAs? String "resource_id_digest_hex" }
    , heapFixture := ← parseHeapFixture (value.getObjValD "heap_fixture") }

def toHeapOp : HeapFixtureOp → HeapOp
  | .allocChannel sender receiver digestHex =>
      .allocChannel sender receiver digestHex
  | .allocMessage source dest label payload seqNo digestHex =>
      .allocMessage source dest label payload seqNo digestHex
  | .allocSession role typeHash digestHex =>
      .allocSession role typeHash digestHex
  | .consume rid =>
      .consume rid

def digestBytes! (hex : String) : List UInt8 :=
  match bytesOfHex? hex with
  | some bytes => bytes
  | none => panic! s!"invalid digest hex fixture: {hex}"

def resourceFixtureValue (fixture : ResourceFixture) : Resource :=
  .message
    { source := fixture.source
    , dest := fixture.dest
    , content := { label := fixture.label, payload := fixture.payload }
    , seqNo := fixture.seqNo }

def stateSummaryJson (state : HeapState) : Json :=
  Json.mkObj
    [ ("active_resource_ids", Json.arr <| (activeResourceIds state).map resourceIdToJson |>.toArray)
    , ("consumed_resource_ids", Json.arr <| (consumedResourceIds state).map resourceIdToJson |>.toArray)
    , ("counter", Json.num state.counter) ]

def proofJson (proof : MerkleProof) : Json :=
  Json.mkObj
    [ ("leaf_hash_hex", Json.str proof.leafHashHex)
    , ("path", Json.arr <| proof.path.map proofStepToJson |>.toArray)
    , ("root_hex", Json.str proof.rootHex) ]

def runFixture (fixture : HeapParityFixture) : Json :=
  let resource := resourceFixtureValue fixture.resourceFixture
  let canonicalBytes := resourceCanonicalBytes resource
  let resourceIdPre := resourceIdPreimage canonicalBytes fixture.resourceFixture.allocationCounter
  let resourceLeafPre :=
    resourceLeafPreimage
      (digestBytes! fixture.resourceFixture.resourceIdDigestHex)
      canonicalBytes
  let nullifierLeafPre :=
    nullifierLeafPreimage (digestBytes! fixture.channelFixture.resourceIdDigestHex)
  let firstRun := applyOps (fixture.heapFixture.operations.map toHeapOp)
  let secondRun := applyOps (fixture.heapFixture.operations.map toHeapOp)
  let commitment : HeapCommitment :=
    { resourceRootHex := fixture.heapFixture.resourceRootHex
    , nullifierRootHex := fixture.heapFixture.nullifierRootHex
    , counter := firstRun.counter }
  let commitmentPre :=
    heapCommitmentPreimage
      (digestBytes! fixture.heapFixture.resourceRootHex)
      (digestBytes! fixture.heapFixture.nullifierRootHex)
      commitment.counter
  let resourceProof :=
    proofFromLevels fixture.heapFixture.resourceLevelsHex fixture.heapFixture.proofIndex
  let nullifierProof :=
    proofFromLevels fixture.heapFixture.nullifierLevelsHex 0
  let activeIdsHex := (activeResourceIds firstRun).map ResourceId.digestHex
  let consumedIdsHex := (consumedResourceIds firstRun).map ResourceId.digestHex
  let sessionLeafHex := fixture.heapFixture.resourceLevelsHex.headD [] |>.getD 1 ""
  let merkleNodePre :=
    merkleNodePreimage
      (digestBytes! fixture.resourceFixture.resourceLeafHex)
      (digestBytes! sessionLeafHex)
  Json.mkObj
    [ ("schema_version", Json.str "lean_heap_parity.v1")
    , ("heap_encoding_version", Json.num heapEncodingVersion)
    , ("hasher", Json.str fixture.hasher)
    , ("resource_fixture", Json.mkObj
        [ ("canonical_bytes_hex", Json.str (hexOfBytes canonicalBytes))
        , ("resource_id_preimage_hex", Json.str (hexOfBytes resourceIdPre))
        , ("resource_leaf_preimage_hex", Json.str (hexOfBytes resourceLeafPre))
        , ("nullifier_leaf_preimage_hex", Json.str (hexOfBytes nullifierLeafPre))
        , ("resource_id_digest_hex", Json.str fixture.resourceFixture.resourceIdDigestHex)
        , ("nullifier_leaf_hex", Json.str fixture.resourceFixture.nullifierLeafHex) ])
    , ("heap_fixture", Json.mkObj
        [ ("active_resource_ids_hex", Json.arr <| activeIdsHex.map Json.str |>.toArray)
        , ("consumed_resource_ids_hex", Json.arr <| consumedIdsHex.map Json.str |>.toArray)
        , ("proof_index", Json.num fixture.heapFixture.proofIndex)
        , ("resource_proof", maybeProofJson resourceProof)
        , ("nullifier_proof", maybeProofJson nullifierProof)
        , ("merkle_node_preimage_hex", Json.str (hexOfBytes merkleNodePre))
        , ("heap_commitment", heapCommitmentToJson commitment)
        , ("heap_commitment_preimage_hex", Json.str (hexOfBytes commitmentPre))
        , ("commitment_hash_hex", Json.str fixture.heapFixture.commitmentHashHex) ])
    , ("replay", Json.mkObj
        [ ("first_run", stateSummaryJson firstRun)
        , ("second_run", stateSummaryJson secondRun)
        , ("stable", Json.bool (firstRun = secondRun))
        , ("active_ids_match_fixture", Json.bool (activeIdsHex = fixture.heapFixture.activeResourceIdsHex))
        , ("consumed_ids_match_fixture", Json.bool (consumedIdsHex = fixture.heapFixture.consumedResourceIdsHex)) ]) ]
where
  maybeProofJson : Option MerkleProof → Json
    | some proof => proofJson proof
    | none => Json.null

def runnerMain (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: heap_parity_runner <fixture-path>"
      pure 1
  | path :: _ =>
      let input ← IO.FS.readFile path
      match Json.parse input with
      | .error err =>
          IO.eprintln s!"invalid JSON: {err}"
          pure 1
      | .ok json =>
          match parseFixture json with
          | .error err =>
              IO.eprintln s!"invalid heap parity fixture: {err}"
              pure 1
          | .ok fixture =>
              IO.println (runFixture fixture).compress
              pure 0

end Runtime.Tests.HeapParityRunner

def main (args : List String) : IO UInt32 :=
  Runtime.Tests.HeapParityRunner.runnerMain args
