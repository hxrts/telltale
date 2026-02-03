import Lean.Data.Json
import Runtime.VM.UnitModel
import Runtime.VM.State
import Protocol.Values

/-!
# VM JSON Serialization

Serialize runtime values and observable trace events for the VM runner.
-/

set_option autoImplicit false

open Lean (Json)

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

/-- Serialize an observable event to JSON (UnitEffect only). -/
def obsEventToJson (ev : ObsEvent UnitEffect) : Json :=
  match ev with
  | .sent edge val _ =>
      Json.mkObj
        [ ("kind", Json.str "sent")
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("value", valueToJson val) ]
  | .received edge val _ =>
      Json.mkObj
        [ ("kind", Json.str "received")
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("value", valueToJson val) ]
  | .offered edge lbl =>
      Json.mkObj
        [ ("kind", Json.str "offered")
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("label", Json.str lbl) ]
  | .chose edge lbl =>
      Json.mkObj
        [ ("kind", Json.str "chose")
        , ("session", Json.num edge.sid)
        , ("sender", Json.str edge.sender)
        , ("receiver", Json.str edge.receiver)
        , ("label", Json.str lbl) ]
  | .opened sid roles =>
      Json.mkObj
        [ ("kind", Json.str "opened")
        , ("session", Json.num sid)
        , ("roles", Json.arr (roles.map Json.str).toArray) ]
  | .closed sid =>
      Json.mkObj
        [ ("kind", Json.str "closed")
        , ("session", Json.num sid) ]
  | .epochAdvanced sid epoch =>
      Json.mkObj
        [ ("kind", Json.str "epoch_advanced")
        , ("session", Json.num sid)
        , ("epoch", Json.num epoch) ]
  | .transferred ep fromCoro toCoro =>
      Json.mkObj
        [ ("kind", Json.str "transferred")
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("from", Json.num fromCoro)
        , ("to", Json.num toCoro) ]
  | .forked sid gsid =>
      Json.mkObj
        [ ("kind", Json.str "forked")
        , ("session", Json.num sid)
        , ("ghost", Json.num gsid) ]
  | .joined sid =>
      Json.mkObj
        [ ("kind", Json.str "joined")
        , ("session", Json.num sid) ]
  | .aborted sid =>
      Json.mkObj
        [ ("kind", Json.str "aborted")
        , ("session", Json.num sid) ]
  | .acquired layer ep =>
      Json.mkObj
        [ ("kind", Json.str "acquired")
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("layer", Json.str layer) ]
  | .released layer ep =>
      Json.mkObj
        [ ("kind", Json.str "released")
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role)
        , ("layer", Json.str layer) ]
  | .invoked ep _ =>
      Json.mkObj
        [ ("kind", Json.str "invoked")
        , ("session", Json.num ep.sid)
        , ("role", Json.str ep.role) ]
  | .tagged _ => Json.mkObj [("kind", Json.str "tagged")]
  | .checked _ permitted =>
      Json.mkObj [("kind", Json.str "checked"), ("permitted", Json.bool permitted)]

/-- Serialize a list of step events to JSON, keeping only observable events. -/
def traceToJson (trace : List (StepEvent UnitEffect)) : Json :=
  let obs := trace.filterMap (fun ev =>
    match ev with
    | .obs o => some (obsEventToJson o)
    | .internal => none)
  Json.arr obs.toArray
