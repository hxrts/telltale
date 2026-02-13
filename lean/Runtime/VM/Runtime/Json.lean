import Lean.Data.Json
import Runtime.VM.Model.UnitModel
import Runtime.VM.Model.State
import Protocol.Values

/-! # VM JSON Serialization

Serialize runtime values and observable trace events for the VM runner.
-/

/-
The Problem. The VM runner needs to output execution traces in a format that can
be consumed by external tools for testing and debugging. JSON is the natural choice
for cross-language interoperability.

Solution Structure. Provides `valueToJson` for serializing runtime `Value` types,
`edgeToJson` for session edges, and `obsEventToJson` for observable trace events.
Each encoder produces well-formed JSON objects with explicit kind tags for
discriminating variants. Used by the VM runner to print execution traces.
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

/-! ### Observable event encoder -/

/-- Serialize a ticked observable event to JSON (UnitEffect only). -/
def obsEventToJson (ev : TickedObsEvent UnitEffect) : Json :=
  match ev.event with
  | .sent edge val _ =>
      Json.mkObj
        [ ("kind", Json.str "sent")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("value", valueToJson val) ]
  | .received edge val _ =>
      Json.mkObj
        [ ("kind", Json.str "received")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("value", valueToJson val) ]
  | .offered edge lbl =>
      Json.mkObj
        [ ("kind", Json.str "offered")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("label", Json.str lbl) ]
  | .chose edge lbl =>
      Json.mkObj
        [ ("kind", Json.str "chose")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("label", Json.str lbl) ]

  -- Session lifecycle events

  | .opened sid roles =>
      Json.mkObj
        [ ("kind", Json.str "opened")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("roles", Json.arr (roles.map Json.str).toArray) ]
  | .closed sid =>
      Json.mkObj
        [ ("kind", Json.str "closed")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid) ]
  | .epochAdvanced sid epoch =>
      Json.mkObj
        [ ("kind", Json.str "epoch_advanced")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
/- ## Structured Block 1 -/
        , ("epoch", Json.num epoch) ]

  -- Runtime ownership/coroutine events

  | .transferred ep fromCoro toCoro =>
      Json.mkObj
        [ ("kind", Json.str "transferred")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("from", Json.num fromCoro)
        , ("to", Json.num toCoro) ]
  | .forked sid gsid =>
      Json.mkObj
        [ ("kind", Json.str "forked")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid)
        , ("ghost", Json.num gsid) ]
  | .joined sid =>
      Json.mkObj
        [ ("kind", Json.str "joined")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid) ]
  | .aborted sid =>
      Json.mkObj
        [ ("kind", Json.str "aborted")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num sid) ]

  -- Guard/effect and monitoring events

  | .acquired layer ep =>
      Json.mkObj
        [ ("kind", Json.str "acquired")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("layer", Json.str layer) ]
  | .released layer ep =>
      Json.mkObj
        [ ("kind", Json.str "released")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("layer", Json.str layer) ]
  | .invoked ep _ =>
      Json.mkObj
        [ ("kind", Json.str "invoked")
        , ("tick", Json.num ev.tick)
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role) ]
  | .tagged _ =>
      Json.mkObj [("kind", Json.str "tagged"), ("tick", Json.num ev.tick)]
  | .checked _ permitted =>
      Json.mkObj
        [ ("kind", Json.str "checked")
/- ## Structured Block 2 -/
        , ("tick", Json.num ev.tick)
        , ("permitted", Json.bool permitted) ]

/-! ### Trace-level serializers -/

/-- Serialize a list of observable events to JSON using session-local ticks. -/
def traceToJson (trace : List (TickedObsEvent UnitEffect)) : Json :=
  let normalized := Runtime.VM.normalizeTrace trace
  Json.arr (normalized.map obsEventToJson).toArray

/-- Serialize a list of observable events to JSON using global ticks. -/
def traceToJsonRaw (trace : List (TickedObsEvent UnitEffect)) : Json :=
  Json.arr (trace.map obsEventToJson).toArray
