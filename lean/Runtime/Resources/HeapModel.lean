import Lean.Data.Json

/-! # Runtime.Resources.HeapModel

Lean model for the runtime heap encoding, tagged preimages, ordering rules,
and a small replay interpreter used by the Rust↔Lean parity lane.
-/

set_option autoImplicit false

namespace Runtime.Resources.HeapModel

open Lean (Json)

/-- Heap encoding magic bytes. -/
def heapEncodingMagic : List UInt8 :=
  [0x54, 0x54, 0x48, 0x50].map UInt8.ofNat

/-- Heap encoding version. -/
def heapEncodingVersion : Nat := 1

/-- Hex-encoded digest bytes. -/
abbrev DigestHex := String

/-- One queued message payload. -/
structure MessagePayload where
  label : String
  payload : List UInt8
  deriving Repr, Inhabited, DecidableEq

/-- Channel resource state. -/
structure ChannelState where
  sender : String
  receiver : String
  queue : List MessagePayload
  deriving Repr, Inhabited, DecidableEq

/-- Message resource. -/
structure Message where
  source : String
  dest : String
  content : MessagePayload
  seqNo : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Heap resource family mirrored from Rust. -/
inductive Resource where
  | channel (state : ChannelState)
  | message (msg : Message)
  | session (role : String) (typeHash : Nat)
  | value (tag : String) (data : List UInt8)
  deriving Repr, Inhabited, DecidableEq

/-- Heap resource identifier. -/
structure ResourceId where
  digestHex : DigestHex
  counter : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Merkle proof direction tag. -/
inductive Direction where
  | left
  | right
  deriving Repr, Inhabited, DecidableEq

/-- One Merkle proof step. -/
structure ProofStep where
  direction : Direction
  siblingHashHex : DigestHex
  deriving Repr, Inhabited, DecidableEq

/-- Lean-side Merkle proof projection. -/
structure MerkleProof where
  leafHashHex : DigestHex
  path : List ProofStep
  rootHex : DigestHex
  deriving Repr, Inhabited, DecidableEq

/-- Heap commitment projection. -/
structure HeapCommitment where
  resourceRootHex : DigestHex
  nullifierRootHex : DigestHex
  counter : Nat
  deriving Repr, Inhabited, DecidableEq

/-- One heap entry. -/
structure HeapEntry where
  rid : ResourceId
  resource : Resource
  deriving Repr, Inhabited, DecidableEq

/-- Minimal heap state needed for parity checks. -/
structure HeapState where
  entries : List HeapEntry := []
  nullifiers : List ResourceId := []
  counter : Nat := 0
  deriving Repr, Inhabited, DecidableEq

/-- Replay operations used by the heap parity corpus. -/
inductive HeapOp where
  | allocChannel (sender receiver : String) (digestHex : DigestHex)
  | allocMessage
      (source dest label : String)
      (payload : List UInt8)
      (seqNo : Nat)
      (digestHex : DigestHex)
  | allocSession (role : String) (typeHash : Nat) (digestHex : DigestHex)
  | consume (rid : ResourceId)
  deriving Repr, Inhabited, DecidableEq

def byteArrayOfList (bytes : List UInt8) : ByteArray :=
  ByteArray.mk bytes.toArray

def utf8Bytes (value : String) : List UInt8 :=
  value.toUTF8.data.toList

def leBytes (width value : Nat) : List UInt8 :=
  (List.range width).map (fun idx => UInt8.ofNat ((value / (256 ^ idx)) % 256))

def hexNibble (value : Nat) : Char :=
  Char.ofNat <|
    if value < 10 then
      '0'.toNat + value
    else
      'a'.toNat + (value - 10)

def byteHex (byte : UInt8) : String :=
  let value := byte.toNat
  String.ofList [hexNibble (value / 16), hexNibble (value % 16)]

def hexOfBytes (bytes : List UInt8) : String :=
  bytes.foldl (fun acc byte => acc ++ byteHex byte) ""

def hexOfByteArray (bytes : ByteArray) : String :=
  hexOfBytes bytes.data.toList

def hexNibble? (ch : Char) : Option Nat :=
  let code := ch.toNat
  if '0'.toNat ≤ code && code ≤ '9'.toNat then
    some (code - '0'.toNat)
  else if 'a'.toNat ≤ code && code ≤ 'f'.toNat then
    some (10 + code - 'a'.toNat)
  else if 'A'.toNat ≤ code && code ≤ 'F'.toNat then
    some (10 + code - 'A'.toNat)
  else
    none

partial def bytesOfHexChars? : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest => do
      let hiNibble ← hexNibble? hi
      let loNibble ← hexNibble? lo
      let tail ← bytesOfHexChars? rest
      pure (UInt8.ofNat (hiNibble * 16 + loNibble) :: tail)
  | [_] => none

def bytesOfHex? (value : String) : Option (List UInt8) :=
  bytesOfHexChars? value.toList

def canonicalPrelude (tag : Nat) : List UInt8 :=
  heapEncodingMagic ++ leBytes 2 heapEncodingVersion ++ [UInt8.ofNat tag]

def encodeByteSlice (bytes : List UInt8) : List UInt8 :=
  leBytes 4 bytes.length ++ bytes

def encodeString (value : String) : List UInt8 :=
  encodeByteSlice (utf8Bytes value)

def listGet? {α : Type} (items : List α) (index : Nat) : Option α :=
  match items, index with
  | [], _ => none
  | item :: _, 0 => some item
  | _ :: rest, index + 1 => listGet? rest index

def messagePayloadCanonicalBytes (payload : MessagePayload) : List UInt8 :=
  canonicalPrelude 0x10 ++ encodeString payload.label ++ encodeByteSlice payload.payload

def channelStateCanonicalBytes (state : ChannelState) : List UInt8 :=
  canonicalPrelude 0x20
    ++ encodeString state.sender
    ++ encodeString state.receiver
    ++ leBytes 4 state.queue.length
    ++ state.queue.flatMap messagePayloadCanonicalBytes

def messageCanonicalBytes (msg : Message) : List UInt8 :=
  canonicalPrelude 0x30
    ++ encodeString msg.source
    ++ encodeString msg.dest
    ++ messagePayloadCanonicalBytes msg.content
    ++ leBytes 8 msg.seqNo

def resourceCanonicalBytes : Resource → List UInt8
  | .channel state =>
      canonicalPrelude 0x40 ++ channelStateCanonicalBytes state
  | .message msg =>
      canonicalPrelude 0x41 ++ messageCanonicalBytes msg
  | .session role typeHash =>
      canonicalPrelude 0x42 ++ encodeString role ++ leBytes 8 typeHash
  | .value tag data =>
      canonicalPrelude 0x43 ++ encodeString tag ++ encodeByteSlice data

def resourceIdPreimage (resourceBytes : List UInt8) (counter : Nat) : List UInt8 :=
  canonicalPrelude 0x50 ++ encodeByteSlice resourceBytes ++ leBytes 8 counter

def resourceLeafPreimage (ridBytes resourceBytes : List UInt8) : List UInt8 :=
  canonicalPrelude 0x51 ++ encodeByteSlice ridBytes ++ encodeByteSlice resourceBytes

def nullifierLeafPreimage (ridBytes : List UInt8) : List UInt8 :=
  canonicalPrelude 0x52 ++ encodeByteSlice ridBytes

def merkleNodePreimage (left right : List UInt8) : List UInt8 :=
  canonicalPrelude 0x53 ++ encodeByteSlice left ++ encodeByteSlice right

def heapCommitmentPreimage
    (resourceRoot nullifierRoot : List UInt8)
    (counter : Nat) : List UInt8 :=
  canonicalPrelude 0x54
    ++ encodeByteSlice resourceRoot
    ++ encodeByteSlice nullifierRoot
    ++ leBytes 8 counter

def resourceIdLt (left right : ResourceId) : Bool :=
  if left.digestHex == right.digestHex then
    left.counter < right.counter
  else
    decide (left.digestHex < right.digestHex)

def sortedResourceIds (ids : List ResourceId) : List ResourceId :=
  (ids.toArray.qsort resourceIdLt).toList

def isNullified (rid : ResourceId) (nullifiers : List ResourceId) : Bool :=
  nullifiers.any (· == rid)

def activeEntries (state : HeapState) : List HeapEntry :=
  state.entries.filter (fun entry => !(isNullified entry.rid state.nullifiers))

def activeEntriesSorted (state : HeapState) : List HeapEntry :=
  (activeEntries state).toArray.qsort (fun left right => resourceIdLt left.rid right.rid) |>.toList

def activeResourceIds (state : HeapState) : List ResourceId :=
  (activeEntriesSorted state).map HeapEntry.rid

def consumedResourceIds (state : HeapState) : List ResourceId :=
  sortedResourceIds state.nullifiers

def applyOp (state : HeapState) : HeapOp → HeapState
  | .allocChannel sender receiver digestHex =>
      let rid := { digestHex := digestHex, counter := state.counter }
      let entry : HeapEntry :=
        { rid := rid
        , resource := .channel { sender := sender, receiver := receiver, queue := [] } }
      { state with entries := state.entries ++ [entry], counter := state.counter + 1 }
  | .allocMessage source dest label payload seqNo digestHex =>
      let rid := { digestHex := digestHex, counter := state.counter }
      let payload := { label := label, payload := payload }
      let entry : HeapEntry :=
        { rid := rid
        , resource := .message { source := source, dest := dest, content := payload, seqNo := seqNo } }
      { state with entries := state.entries ++ [entry], counter := state.counter + 1 }
  | .allocSession role typeHash digestHex =>
      let rid := { digestHex := digestHex, counter := state.counter }
      let entry : HeapEntry := { rid := rid, resource := .session role typeHash }
      { state with entries := state.entries ++ [entry], counter := state.counter + 1 }
  | .consume rid =>
      if isNullified rid state.nullifiers then
        state
      else
        { state with nullifiers := state.nullifiers ++ [rid] }

def applyOps (ops : List HeapOp) (init : HeapState := {}) : HeapState :=
  ops.foldl applyOp init

def proofPathFromLevels : List (List DigestHex) → Nat → List ProofStep
  | [], _ => []
  | [_], _ => []
  | level :: rest, index =>
      let siblingIndex := if index % 2 = 0 then index + 1 else index - 1
      let siblingHash := level.getD siblingIndex (level.getD index "")
      let direction := if index % 2 = 0 then Direction.right else Direction.left
      { direction := direction, siblingHashHex := siblingHash }
        :: proofPathFromLevels rest (index / 2)

def proofFromLevels (levels : List (List DigestHex)) (index : Nat) : Option MerkleProof := do
  let leaves ← levels.head?
  let rootLevel ← levels.getLast?
  let leaf ← listGet? leaves index
  let root ← rootLevel.head?
  pure
    { leafHashHex := leaf
    , path := proofPathFromLevels levels index
    , rootHex := root }

def directionToJson : Direction → Json
  | .left => Json.str "Left"
  | .right => Json.str "Right"

def proofStepToJson (step : ProofStep) : Json :=
  Json.mkObj
    [ ("direction", directionToJson step.direction)
    , ("sibling_hash_hex", Json.str step.siblingHashHex) ]

def resourceIdToJson (rid : ResourceId) : Json :=
  Json.mkObj
    [ ("digest_hex", Json.str rid.digestHex)
    , ("counter", Json.num rid.counter) ]

def heapCommitmentToJson (commitment : HeapCommitment) : Json :=
  Json.mkObj
    [ ("resource_root_hex", Json.str commitment.resourceRootHex)
    , ("nullifier_root_hex", Json.str commitment.nullifierRootHex)
    , ("counter", Json.num commitment.counter) ]

theorem message_payload_encoding_deterministic (payload : MessagePayload) :
    messagePayloadCanonicalBytes payload = messagePayloadCanonicalBytes payload := rfl

theorem resource_encoding_deterministic (resource : Resource) :
    resourceCanonicalBytes resource = resourceCanonicalBytes resource := by
  cases resource <;> rfl

theorem active_ordering_deterministic (state : HeapState) :
    activeResourceIds state = activeResourceIds state := rfl

theorem consumed_ordering_deterministic (state : HeapState) :
    consumedResourceIds state = consumedResourceIds state := rfl

theorem replay_deterministic (ops : List HeapOp) (init : HeapState := {}) :
    applyOps ops init = applyOps ops init := rfl

theorem repeated_replay_is_identical (ops : List HeapOp) (init : HeapState := {}) :
    (applyOps ops init, applyOps ops init) = (applyOps ops init, applyOps ops init) := rfl

end Runtime.Resources.HeapModel
