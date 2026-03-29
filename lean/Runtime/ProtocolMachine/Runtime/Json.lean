import Lean.Data.Json
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Model.State
import Protocol.Values

/-! # protocol machine JSON Serialization

Serialize runtime values and observable trace events for the protocol machine runner.
-/

/-
The Problem. The protocol machine runner needs to output execution traces in a format that can
be consumed by external tools for testing and debugging. JSON is the natural choice
for cross-language interoperability.

Solution Structure. Provides `valueToJson` for serializing runtime `Value` types,
`edgeToJson` for session edges, and `obsEventToJson` for observable trace events.
Each encoder produces well-formed JSON objects with explicit kind tags for
discriminating variants. Used by the protocol machine runner to print execution traces.
-/

set_option autoImplicit false

open Lean (Json)

/-! ## JSON Encoders -/

/-! ### Value and edge encoders -/

/-- Serialize a runtime Value to JSON. -/
def valueToJson : Value → Json
  | .unit => Json.mkObj [("kind", Json.str "unit")]
  | .bool b => Json.mkObj [("kind", Json.str "bool"), ("value", Json.bool b)]
  | .nat n => Json.mkObj [("kind", Json.str "nat"), ("value", Json.num n)]
  | .string s => Json.mkObj [("kind", Json.str "string"), ("value", Json.str s)]
  | .prod a b => Json.mkObj
      [("kind", Json.str "prod"), ("left", valueToJson a), ("right", valueToJson b)]
  | .chan ep => Json.mkObj
      [("kind", Json.str "chan"), ("session", Json.num ep.sid), ("role", Json.str ep.role)]

/-- Serialize an Edge to JSON. -/
def edgeToJson (e : Edge) : Json :=
  Json.mkObj
    [ ("session", Json.num e.sid)
    , ("sender", Json.str e.sender)
    , ("receiver", Json.str e.receiver) ]

private def sessionTerminalReasonTag : SessionTerminalReason → String
  | .closed _ => "closed"
  | .cancelled _ => "cancelled"
  | .aborted _ => "aborted"
  | .faulted _ => "faulted"

private def sessionTerminalReasonText : SessionTerminalReason → String
  | .closed reason => reason
  | .cancelled reason => reason
  | .aborted reason => reason
  | .faulted reason => reason

private def ownershipTerminalReasonToJson (reason : OwnershipTerminalReason) : Json :=
  match reason with
  | .ownerDied ownerId =>
      Json.mkObj
        [ ("kind", Json.str "owner_died")
        , ("owner_id", Json.str ownerId) ]
  | .transferAbandoned ownerId claimId =>
      Json.mkObj
        [ ("kind", Json.str "transfer_abandoned")
        , ("owner_id", Json.str ownerId)
        , ("claim_id", Json.num claimId) ]
  | .transferCommitFailed ownerId claimId detail =>
      Json.mkObj
        [ ("kind", Json.str "transfer_commit_failed")
        , ("owner_id", Json.str ownerId)
        , ("claim_id", Json.num claimId)
        , ("reason", Json.str detail) ]

/-! ### Observable event encoder -/

/-- Serialize a ticked observable event to JSON (UnitEffect only). -/
def obsEventToJson (ev : TickedObsEvent UnitEffect) : Json :=
  let withSchema (fields : List (String × Json)) : Json :=
    Json.mkObj <| ("schema_version", Json.str "lean_bridge.v1") :: fields
  match ev.event with
  | .sent edge val seqNo =>
      let labelField :=
        match val with
        | .string s => [("label", Json.str s)]
        | _ => []
      withSchema <|
        [ ("kind", Json.str "sent")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("sequence", Json.num seqNo)
        , ("value", valueToJson val) ] ++ labelField
  | .received edge val seqNo =>
      let labelField :=
        match val with
        | .string s => [("label", Json.str s)]
        | _ => []
      withSchema <|
        [ ("kind", Json.str "received")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("sequence", Json.num seqNo)
        , ("value", valueToJson val) ] ++ labelField
  | .offered edge lbl =>
      withSchema
        [ ("kind", Json.str "sent")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("label", Json.str lbl) ]
  | .chose edge lbl =>
      withSchema
        [ ("kind", Json.str "received")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("label", Json.str lbl) ]

  /- ## Session lifecycle events -/

  -- Session lifecycle events

  | .opened sid roles =>
      withSchema
        [ ("kind", Json.str "opened")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("role", Json.str (String.intercalate "," roles))
        , ("roles", Json.arr (roles.map Json.str).toArray) ]
  | .closed sid =>
      withSchema
        [ ("kind", Json.str "closed")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid) ]
  | .epochAdvanced sid epoch =>
      withSchema
        [ ("kind", Json.str "epoch_advanced")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
/- ## Structured Block 1 -/
        , ("epoch", Json.num epoch) ]

  -- Runtime ownership/coroutine events

  | .transferred ep fromCoro toCoro =>
      withSchema
        [ ("kind", Json.str "transferred")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("from", Json.num fromCoro)
        , ("to", Json.num toCoro) ]
  | .forked sid gsid =>
      withSchema
        [ ("kind", Json.str "forked")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("ghost", Json.num gsid) ]
  | .joined sid =>
      withSchema
        [ ("kind", Json.str "joined")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid) ]
  | .aborted sid =>
      withSchema
        [ ("kind", Json.str "aborted")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid) ]
  | .sessionTerminal sid reason =>
      withSchema
        [ ("kind", Json.str "session_terminal")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("reason_kind", Json.str (sessionTerminalReasonTag reason))
        , ("reason", Json.str (sessionTerminalReasonText reason)) ]

  -- Guard/effect and monitoring events

  | .acquired layer ep =>
      withSchema
        [ ("kind", Json.str "acquired")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("layer", Json.str layer) ]
  | .released layer ep =>
      withSchema
        [ ("kind", Json.str "released")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("layer", Json.str layer) ]
  | .invoked ep _ =>
      withSchema
        [ ("kind", Json.str "invoked")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role) ]
  | .tagged _ =>
      withSchema [("kind", Json.str "tagged"), ("tick", Json.num ev.tick)]
  | .checked _ permitted =>
      withSchema
        [ ("kind", Json.str "checked")
/- ## Structured Block 2 -/
        , ("tick", Json.num ev.tick)
        , ("permitted", Json.bool permitted) ]
  | .failureBranchEntered sid coroId faultClass =>
      withSchema
        [ ("kind", Json.str "failure_branch_entered")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("coro_id", Json.num coroId)
        , ("fault", Json.str faultClass) ]
  | .timeoutIssued site untilTick witnessId =>
      withSchema
        [ ("kind", Json.str "timeout_issued")
        , ("tick", Json.num ev.tick)
        , ("site", Json.str site)
        , ("until_tick", Json.num untilTick)
        , ("witness_id", Json.num witnessId) ]
  | .cancellationRequested sid witnessId ownerId reason =>
      withSchema
        [ ("kind", Json.str "cancellation_requested")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("witness_id", Json.num witnessId)
        , ("owner_id", Json.str ownerId)
        , ("reason", ownershipTerminalReasonToJson reason) ]
  | .cancelled sid witnessId reason =>
      withSchema
        [ ("kind", Json.str "cancelled")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("witness_id", Json.num witnessId)
        , ("reason", ownershipTerminalReasonToJson reason) ]

/-! ### Trace-level serializers -/

/-- Serialize a list of observable events to JSON using session-local ticks. -/
def traceToJson (trace : List (TickedObsEvent UnitEffect)) : Json :=
  let normalized := Runtime.ProtocolMachine.normalizeTrace trace
  Json.arr (normalized.map obsEventToJson).toArray

/-- Serialize a list of observable events to JSON using global ticks. -/
def traceToJsonRaw (trace : List (TickedObsEvent UnitEffect)) : Json :=
  Json.arr (trace.map obsEventToJson).toArray
