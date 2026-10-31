import Runtime.Tests.ProtocolMachineRunner.Core

/-! # protocol machine Runner: trace validation

Trace-validation payload parsing and structured error reporting for the
`protocol_machine_runner` executable (session trace specs, event validation).
-/

set_option autoImplicit false

open Lean (Json)
open Choreography.Projection.Json

structure SessionTraceSpec where
  sid : Nat
  roles : List String
  actions : List (String × String × String)

structure TraceValidationState where
  opened : List Nat := []
  closed : List Nat := []
  outstanding : List (Nat × String × String × String) := []

def structuredError (code path message : String) : Json :=
  Json.mkObj
    [ ("code", Json.str code)
    , ("path", Json.str path)
    , ("message", Json.str message) ]

def validationResponse (errors : List Json) : Json :=
  Json.mkObj
    [ ("valid", Json.bool errors.isEmpty)
    , ("errors", Json.arr errors.toArray) ]

mutual
  def collectTraceActions : GlobalType → List (String × String × String)
    | .end => []
    | .var _ => []
    | .mu _ body => collectTraceActions body
    | .comm sender receiver branches =>
        collectTraceActionsBranches sender receiver branches
    | .delegate _ _ _ _ cont => collectTraceActions cont

  def collectTraceActionsBranches (sender receiver : String)
      : List (SessionTypes.GlobalType.Label × GlobalType) → List (String × String × String)
    | [] => []
    | (label, cont) :: rest =>
        (sender, receiver, label.name) ::
          collectTraceActions cont ++ collectTraceActionsBranches sender receiver rest
end

def sameRoleSet (left right : List String) : Bool :=
  let left' := left.eraseDups
  let right' := right.eraseDups
  left'.length == right'.length && left'.all (fun role => right'.contains role)

def findSessionSpec? (specs : List SessionTraceSpec) (sid : Nat) : Option SessionTraceSpec :=
  specs.find? (fun spec => spec.sid == sid)

def removeOutstanding? (target : Nat × String × String × String)
    (outstanding : List (Nat × String × String × String)) :
    Option (List (Nat × String × String × String)) :=
  match outstanding with
  | [] => none
  | head :: tail =>
      if head = target then
        some tail
      else
        match removeOutstanding? target tail with
        | some rest => some (head :: rest)
        | none => none

def jsonStringList (value : Json) : Except String (List String) := do
  let arr ← value.getArr?
  arr.toList.mapM Json.getStr?

def requiredStringField (value : Json) (field : String) : Except String String := do
  let fieldValue ← value.getObjVal? field
  fieldValue.getStr?

def requiredNatField (value : Json) (field : String) : Except String Nat := do
  let fieldValue ← value.getObjVal? field
  fieldValue.getNat?

def requiredRolesField (value : Json) : Except String (List String) := do
  match value.getObjVal? "roles" with
  | .ok fieldValue =>
      jsonStringList fieldValue
  | .error _ =>
      let roleField ← value.getObjVal? "role"
      let roleString ← roleField.getStr?
      pure <| roleString.splitOn ","

def fieldError (idx : Nat) (field code detail : String) : Json :=
  structuredError code s!"trace[{idx}].{field}" detail

def eventError (idx : Nat) (code detail : String) : Json :=
  structuredError code s!"trace[{idx}]" detail

def indexedChoreographies (items : List Json) : Except String (List (Nat × Json)) :=
  let rec go (idx : Nat) (remaining : List Json) : List (Nat × Json) :=
    match remaining with
    | [] => []
    | item :: rest => (idx, item) :: go (idx + 1) rest
  pure (go 0 items)

def validateTraceEvents (specs : List SessionTraceSpec) (events : List Json) : List Json :=
  let rec go (idx : Nat) (st : TraceValidationState) (remaining : List Json) :
      Except Json TraceValidationState :=
    match remaining with
    | [] =>
        if st.outstanding.isEmpty then
          pure st
        else
          throw <| structuredError
            "trace.unmatched_send"
            "trace"
            "trace ended with unmatched send events"
    | event :: rest => do
        let kind ←
          match requiredStringField event "kind" with
          | .ok value => pure value
          | .error detail => throw <| fieldError idx "kind" "trace.invalid_event" detail
        match kind with
        | "opened" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            let roles ←
              match requiredRolesField event with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "roles" "trace.invalid_roles" detail
            match findSessionSpec? specs sid with
            | none =>
                throw <| eventError idx "trace.unknown_session" s!"unknown session {sid}"
            | some spec =>
                if st.opened.contains sid then
                  throw <| eventError idx "trace.duplicate_open" s!"session {sid} opened twice"
                else if !(sameRoleSet roles spec.roles) then
                  throw <|
                    structuredError
                      "trace.role_mismatch"
                      s!"trace[{idx}].roles"
                      s!"session {sid} roles do not match choreography"
                else
                  go (idx + 1) { st with opened := sid :: st.opened } rest
        | "closed" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            if !(st.opened.contains sid) then
              throw <| eventError idx "trace.close_before_open" s!"session {sid} closed before open"
            else if st.outstanding.any (fun (osid, _, _, _) => osid == sid) then
              throw <| eventError idx "trace.close_with_outstanding" s!"session {sid} closed with outstanding sends"
            else
              go (idx + 1) { st with closed := sid :: st.closed } rest
        | "sent" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            let sender ←
              match requiredStringField event "sender" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "sender" "trace.invalid_sender" detail
            let receiver ←
              match requiredStringField event "receiver" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "receiver" "trace.invalid_receiver" detail
            let label ←
              match requiredStringField event "label" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "label" "trace.invalid_label" detail
            if !(st.opened.contains sid) then
              throw <| eventError idx "trace.send_before_open" s!"session {sid} sent before open"
            else
              match findSessionSpec? specs sid with
              | none =>
                  throw <| eventError idx "trace.unknown_session" s!"unknown session {sid}"
              | some spec =>
                  if spec.actions.contains (sender, receiver, label) then
                    go (idx + 1)
                      { st with outstanding := st.outstanding ++ [(sid, sender, receiver, label)] }
                      rest
                  else
                    throw <|
                      structuredError
                        "trace.unknown_action"
                        s!"trace[{idx}].label"
                        s!"{sender}->{receiver} label '{label}' is not permitted by the choreography"
        | "received" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            let sender ←
              match requiredStringField event "sender" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "sender" "trace.invalid_sender" detail
            let receiver ←
              match requiredStringField event "receiver" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "receiver" "trace.invalid_receiver" detail
            let label ←
              match requiredStringField event "label" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "label" "trace.invalid_label" detail
            if !(st.opened.contains sid) then
              throw <| eventError idx "trace.recv_before_open" s!"session {sid} received before open"
            else
              let action := (sid, sender, receiver, label)
              match removeOutstanding? action st.outstanding with
              | some outstanding =>
                  go (idx + 1) { st with outstanding := outstanding } rest
              | none =>
                  throw <|
                    structuredError
                      "trace.unmatched_receive"
                      s!"trace[{idx}]"
                      s!"{sender}->{receiver} label '{label}' had no matching send"
        | _ =>
            go (idx + 1) st rest
  match go 0 {} events with
  | .ok _ => []
  | .error err => [err]

def parseValidateTracePayload (payload : Json) :
    Except String (List SessionTraceSpec × List Json) := do
  let choreosValue ← payload.getObjVal? "choreographies"
  let choreosArr ← choreosValue.getArr?
  let traceValue ← payload.getObjVal? "trace"
  let traceArr ← traceValue.getArr?
  let indexed ← indexedChoreographies choreosArr.toList
  let choreos ←
    indexed.mapM (fun
      | (sid, choreoJson) => do
      let (g, roles) ← parseChoreo choreoJson
      pure {
        sid := sid
        roles := roles
        actions := collectTraceActions g
      })
  pure (choreos, traceArr.toList)

def parseValidateSimulationTracePayload (payload : Json) :
    Except String (List SessionTraceSpec × List Json) := do
  let inputJson ← payload.getObjVal? "input"
  let globalJson := inputJson.getObjValD "global_type"
  let global ← globalTypeFromJson globalJson
  let traceValue ← payload.getObjVal? "trace"
  let traceArr ← traceValue.getArr?
  pure ([{
    sid := 0
    roles := global.roles
    actions := collectTraceActions global
  }], traceArr.toList)
