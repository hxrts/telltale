import Runtime.Tests.Main.Helpers

/-! # Runtime tests: communication replay and admission guards

Tests 38-43 of the `runtime_tests` executable: transfer faults, communication replay
modes, payload size gates, and strict-schema send/recv rejection.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

open SessionTypes.LocalTypeR
open SessionTypes.GlobalType

/-- Tests 38-43: transfer faults, replay modes, payload and schema guards. -/
def runReplayGuardTests
    (stPlan : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify) :
    IO Unit := do
  -- Test 38: transfer fault helper emits normalized transfer target fault message.
  let transferEp : Endpoint := { sid := 9, role := "A" }
  let badTransferRegs : RegFile :=
    #[ .chan transferEp
     , .string "not-a-target"
     , .unit, .unit, .unit, .unit, .unit, .unit ]
  let badTransferCoro : CoroutineState UnitGuard UnitEffect :=
    { mkReadyCoro 0 with regs := badTransferRegs, ownedEndpoints := [transferEp] }
  let badTransferPack := stepTransfer stPlan badTransferCoro 0 1 0
  expect (hasTransferFaultMsg badTransferPack.res "bad transfer target")
    "transfer target type fault did not use normalized transfer fault helper"

  -- Test 39: communication replay off mode accepts duplicate identities.
  let offStart := withCommReplayMode emptyState .off
  let offDuplicateOk :=
    match commConsumeReceiveIdentity offStart 0 (sampleCommIdentity 0) with
    | .ok (_, offNext) =>
        match commConsumeReceiveIdentity offNext 1 (sampleCommIdentity 0) with
        | .ok _ => true
        | .error _ => false
    | .error _ => false
  expect offDuplicateOk "comm replay off mode rejected duplicate identity"

  -- Test 40: sequence mode rejects out-of-order sequence numbers.
  let seqStart := withCommReplayMode emptyState .sequence
  let seqMismatchRejected :=
    match commConsumeReceiveIdentity seqStart 0 (sampleCommIdentity 0) with
    | .ok (_, seqNext) =>
        match commConsumeReceiveIdentity seqNext 1 (sampleCommIdentity 2) with
        | .error msg => msg.startsWith "comm_replay.sequence_mismatch"
        | .ok _ => false
    | .error _ => false
  expect seqMismatchRejected "comm replay sequence mode accepted out-of-order sequence number"

  -- Test 41: nullifier mode rejects duplicate identities.
  let nullStart := withCommReplayMode emptyState .nullifier
  let nullDuplicateRejected :=
    match commConsumeReceiveIdentity nullStart 0 (sampleCommIdentity 3) with
    | .ok (_, nullNext) =>
        match commConsumeReceiveIdentity nullNext 1 (sampleCommIdentity 3) with
        | .error msg => msg = "comm_replay.duplicate"
        | .ok _ => false
    | .error _ => false
  expect nullDuplicateRejected "comm replay nullifier mode accepted duplicate identity"

  -- Test 41a: sequence-bound nullifier identity accepts identical content with a fresh seqNo.
  let seqBoundResendOk :=
    match commConsumeReceiveIdentity nullStart 0 (sampleCommIdentity 3) with
    | .ok (_, nullNext) =>
        match commConsumeReceiveIdentity nullNext 1 (sampleCommIdentity 4) with
        | .ok _ => true
        | .error _ => false
    | .error _ => false
  expect seqBoundResendOk "sequence-bound nullifier identity rejected fresh sequence number"

  -- Test 41b: content-only nullifier identity rejects a resend with a fresh seqNo.
  let contentStart :=
    { nullStart with config :=
        { nullStart.config with communicationNullifierIdentity := .contentOnly } }
  let contentResendRejected :=
    match commConsumeReceiveIdentity contentStart 0 (sampleCommIdentity 3) with
    | .ok (_, contentNext) =>
        match commConsumeReceiveIdentity contentNext 1 (sampleCommIdentity 4) with
        | .error msg => msg = "comm_replay.duplicate"
        | .ok _ => false
    | .error _ => false
  expect contentResendRejected "content-only nullifier identity accepted resent content"

  -- Test 42: payload size gate rejects oversized send payloads.
  let sidPayload := 0
  let epA : Endpoint := { sid := sidPayload, role := "A" }
  let epB : Endpoint := { sid := sidPayload, role := "B" }
  let rolesPayload : RoleSet := ["A", "B"]
  let edgesPayload : List Edge := rolesPayload.foldr (fun src acc =>
    let out : List Edge := rolesPayload.map (fun dst =>
      ({ sid := sidPayload, sender := src, receiver := dst } : Edge))
    out ++ acc) []
  let buffersPayload := signedBuffersEnsure ([] : SignedBuffers UnitVerify) edgesPayload
  let sessionPayload : SessionState UnitVerify :=
    { scope := { id := sidPayload }
    , sid := sidPayload
    , roles := rolesPayload
    , endpoints := [epA, epB]
    , localTypes := [(epA, .send "B" .string .end_), (epB, .recv "A" .string .end_)]
    , traces := initDEnv sidPayload rolesPayload
    , buffers := buffersFor buffersPayload sidPayload
    , handlers := edgesPayload.map (fun e => (e, 0))
    , epoch := 0
    , phase := .active }
  let oversizedPayload := String.ofList (List.replicate 256 'x')
  let regsPayload : RegFile := #[.chan epA, .string oversizedPayload, .unit, .unit, .unit, .unit, .unit, .unit]
  let senderPayload : CoroutineState UnitGuard UnitEffect :=
    { mkReadyCoro 999 with regs := regsPayload, ownedEndpoints := [epA] }
  let stPayload : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
    { emptyState with
        config := { emptyState.config with maxPayloadBytes := 8 }
        coroutines := #[senderPayload]
        buffers := buffersPayload
        sessions := [(sidPayload, sessionPayload)] }
  let payloadResult :=
    match (stepSend stPayload senderPayload 0 1).res.status with
    | .faulted (.specFault msg) =>
        (msg.startsWith "send payload exceeds max_payload_bytes=", s!"spec_fault:{msg}")
    | .faulted _ => (false, "faulted_non_spec")
    | .blocked _ => (false, "blocked")
    | _ => (false, "non_fault_status")
  let payloadRejected := payloadResult.fst
  let payloadOutcome := payloadResult.snd
  expect payloadRejected s!"payload size gate did not reject oversized payload ({payloadOutcome})"

  -- Test 43: strict-schema mode rejects annotationless single-branch send/recv paths.
  let sidStrict := sidPayload + 1
  let epStrictA : Endpoint := { sid := sidStrict, role := "A" }
  let epStrictB : Endpoint := { sid := sidStrict, role := "B" }
  let rolesStrict : RoleSet := ["A", "B"]
  let edgesStrict : List Edge := rolesStrict.foldr (fun src acc =>
    let out : List Edge := rolesStrict.map (fun dst =>
      ({ sid := sidStrict, sender := src, receiver := dst } : Edge))
    out ++ acc) []
  let buffersStrict := signedBuffersEnsure ([] : SignedBuffers UnitVerify) edgesStrict
  let sessionStrict : SessionState UnitVerify :=
    { scope := { id := sidStrict }
    , sid := sidStrict
    , roles := rolesStrict
    , endpoints := [epStrictA, epStrictB]
    , localTypes := [(epStrictA, .select "B" [("msg", .end_)]), (epStrictB, .branch "A" [("msg", .end_)])]
    , traces := initDEnv sidStrict rolesStrict
    , buffers := buffersFor buffersStrict sidStrict
    , handlers := edgesStrict.map (fun e => (e, 0))
    , epoch := 0
    , phase := .active }
  let regsStrict : RegFile := #[.chan epStrictA, .nat 1, .unit, .unit, .unit, .unit, .unit, .unit]
  let senderStrict : CoroutineState UnitGuard UnitEffect :=
    { mkReadyCoro 1000 with regs := regsStrict, ownedEndpoints := [epStrictA] }
  let stStrictCfg : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
    { emptyState with
        config := { emptyState.config with payloadValidationMode := .strictSchema }
        coroutines := #[senderStrict]
        buffers := buffersStrict
        sessions := [(sidStrict, sessionStrict)] }
  let strictSchemaRejected :=
    match (stepSend stStrictCfg senderStrict 0 1).res.status with
    | .faulted (.specFault msg) =>
        msg.endsWith "requires explicit ValType annotation in strict_schema mode"
    | _ => false
  expect strictSchemaRejected
    "strict-schema mode did not reject annotationless send/recv path"
