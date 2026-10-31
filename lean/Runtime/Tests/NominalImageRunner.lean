import Lean.Data.Json
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Runtime.Loader
import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.ProtocolMachine.Runtime.Json
import Choreography.Projection.Json
import Runtime.Tests.NominalImageRunner.Parsing

/-! Executable-image operation of the existing protocol-machine runner.
The input contains actual bytecode and typed nominal outcomes. Communication
projections are validated but never regenerated into replacement bytecode. -/

set_option autoImplicit false
namespace Runtime.Tests.NominalImageRunner
open Lean (Json)
open Runtime.ProtocolMachine.Model
open Choreography.Projection.Json

private def statusJson : EffectOutcomeStatus → Json
  | .success => Json.mkObj [("status", "success")]
  | .blocked => Json.mkObj [("status", "blocked")]
  | .failure kind message => Json.mkObj [("status", "failure"), ("kind", Json.str kind), ("message", Json.str message)]
private def witnessJson (witness : SessionTypes.ReadinessWitness) : Json :=
  Json.mkObj [("witness_id", Json.num witness.witnessId), ("session_id", Json.num witness.sessionId),
    ("owner_id", Json.str witness.ownerId), ("generation", Json.num witness.generation),
    ("predicate_ref", Json.str witness.predicateRef), ("scope", match witness.scope with
      | .session => Json.str "Session"
      | .fragments roles => Json.mkObj [("Fragments", Json.arr (roles.map Json.str).toArray)])]
private def ownerJson (owner : SessionTypes.ModelOwner) : Json :=
  Json.mkObj [("session_id", Json.num owner.sessionId), ("owner_id", Json.str owner.ownerId),
    ("generation", Json.num owner.generation), ("scope", match owner.scope with
      | .session => Json.str "Session"
      | .fragments roles => Json.mkObj [("Fragments", Json.arr (roles.map Json.str).toArray)])]
private def resultJson : Except String NominalCommandValue → Json
  | .ok (.bool value) => Json.mkObj [("Ok", Json.mkObj [("Bool", Json.bool value)])]
  | .ok (.readiness witness) => Json.mkObj [("Ok", Json.mkObj [("Readiness", witnessJson witness)])]
  | .error reason => Json.mkObj [("Err", Json.str reason)]
private def optionalNat (value : Option Nat) : Json := value.map Json.num |>.getD Json.null

private def nominalResponseJson (response : Option EffectResponse) : Except String Json :=
  match response with
  | none => pure Json.null
  | some (.nominalCommand reply) => pure (Json.mkObj [
      ("kind", "nominal_command"), ("invocation", Json.num reply.invocation), ("result", resultJson reply.result)])
  | some .release => pure (Json.mkObj [("kind", "release")])
  | some _ => throw "unsupported typed nominal response cannot be erased"

private def exchangeJson (exchange : EffectExchangeRecord) : Except String Json := do
  let request ← match exchange.request.body with
    | .nominalCommand request => pure (Json.mkObj [
        ("invocation", Json.num request.invocation), ("session", Json.num request.session),
        ("coroutine", Json.num request.coroutine), ("role", Json.str request.role),
        ("interface", Json.str request.declaration.interfaceName),
        ("operation", Json.str request.declaration.operationName),
        ("may_block", Json.bool request.declaration.mayBlock),
        ("readiness_predicate", request.declaration.readinessPredicate.map Json.str |>.getD Json.null)])
    | _ => throw "unsupported typed nominal request cannot be erased"
  let response ← nominalResponseJson exchange.outcome.response
  return Json.mkObj [("effect_id", Json.num exchange.effectId),
    ("issued_at", Json.num exchange.orderingKey), ("observed_at", optionalNat exchange.observedAt),
    ("handler_identity", Json.str exchange.handlerIdentity), ("request", request),
    ("status", statusJson exchange.outcome.status),
    ("accepted_status", statusJson (exchange.outcome.acceptedStatusFor exchange.request.body)),
    ("response", response)]

private def effectStatus : OutstandingEffectStatus → String
  | .pending => "pending" | .blocked => "blocked" | .succeeded => "succeeded"
  | .failed => "failed" | .cancelled => "cancelled" | .invalidated => "invalidated"
private def coroStatus (status : CoroStatus UnitGuard) : String := match status with
  | .ready => "ready" | .blocked _ => "blocked"
  | .done => "done" | .faulted _ => "faulted" | .speculating => "speculating"

private def levelName : AgreementLevel → String
  | .none => "none" | .provisional => "provisional" | .softSafe => "soft_safe" | .finalized => "finalized"
private def profileJson (profile : AgreementProfile) : Json :=
  let visibility := match profile.visibility with
    | .immediate => "immediate" | .pending => "pending" | .blockedUntilFinalized => "blocked_until_finalized"
  let rule := match profile.rule with
    | .noAgreement => Json.str "no_agreement" | .anyParticipant => Json.str "any_participant"
    | .unanimous => Json.str "unanimous"
    | .threshold required => Json.mkObj [("threshold", Json.mkObj [("required_participants", Json.num required)])]
    | .named name => Json.mkObj [("named", Json.mkObj [("rule_name", Json.str name)])]
  let evidence := match profile.requiredEvidenceKind with
    | .witness => "witness" | .certificate => "certificate" | .commitFact => "commit_fact"
    | .publication => "publication" | .materialization => "materialization"
  Json.mkObj [("profile_name", Json.str profile.profileName), ("visibility", Json.str visibility),
    ("rule", rule), ("usable_at", Json.str (levelName profile.usableAt)),
    ("finalized_at", Json.str (levelName profile.finalizedAt)), ("required_evidence_kind", Json.str evidence)]
private def declarationJson (declaration : NominalCommandDeclaration) : Json :=
  Json.mkObj ([("interface", Json.str declaration.interfaceName),
      ("operation", Json.str declaration.operationName), ("may_block", Json.bool declaration.mayBlock)] ++
    (declaration.readinessPredicate.map (fun predicate => [("readiness_predicate", Json.str predicate)]) |>.getD []))
private def callJson (start : Nat) (call : NominalCommandCall) : Json :=
  Json.mkObj [("declaration", declarationJson call.declaration),
    ("enclosing_operation", Json.str call.enclosingOperation), ("role", Json.str call.role),
    ("agreement_profile", profileJson call.agreementProfile),
    ("progress_contract", Json.str call.progressContract), ("progress_window", Json.str call.progressWindow),
    ("budget_ticks", Json.num call.budgetTicks), ("result", Json.num call.result),
    ("on_ok", Json.num (call.onOk - start : Nat)), ("on_err", Json.num (call.onErr - start : Nat))]
private def continuationJson (start : Nat) (holder : Option NominalCommandContinuation) : Json :=
  match holder with
  | none => Json.null
  | some original => Json.mkObj [("invocation", Json.num original.invocation),
      ("original_pc", Json.num (original.pc - start : Nat)), ("call", callJson start original.call),
      ("issued_at", Json.num original.issuedAt), ("handler_identity", Json.str original.handlerIdentity),
      ("returned", (original.returned.map resultJson).getD Json.null),
      ("original_owner", (original.originalOwner.map ownerJson).getD Json.null),
      ("readiness_owner", if original.call.declaration.readinessPredicate.isSome then
        (original.originalOwner.map ownerJson).getD Json.null else Json.null),
      ("validation_failure", (original.validationFailure.map fun failure =>
        Json.mkObj [("kind", Json.str failure.1), ("message", Json.str failure.2)]).getD Json.null)]
private def faultJson (status : CoroStatus UnitGuard) : Except String Json := match status with
  | .faulted (.effectFault kind message) => pure (Json.mkObj [("kind", "invoke"),
      ("failure", Json.mkObj [("kind", Json.str kind), ("message", Json.str message)])])
  | .faulted .outOfRegisters => pure (Json.mkObj [("kind", "out_of_registers")])
  | .faulted (.outputCondition predicate) => pure (Json.mkObj [("kind", "output_condition"), ("predicate_ref", Json.str predicate)])
  | .faulted _ => throw "unsupported terminal fault family cannot be erased by nominal comparison"
  | _ => pure Json.null

private def registryJson (state : SessionTypes.ModelOwnershipState) : Json :=
  Json.mkObj [("current", state.current.map ownerJson |>.getD Json.null),
    ("transfer_pending", Json.bool state.transferPending),
    ("issued", Json.arr (state.issuedReadiness.map witnessJson).toArray),
    ("consumed", Json.arr (state.consumedWitnesses.map Json.num).toArray),
    ("next_witness_id", Json.num state.nextWitnessId),
    ("audit", Json.arr (state.readinessAudit.map fun event => Json.mkObj [
      ("tick", optionalNat event.tick), ("artifact", Json.mkObj [("Readiness", witnessJson event.witness)]),
      ("event", Json.str event.event), ("reason", event.reason.map Json.str |>.getD Json.null)]).toArray)]

/-- Actual model ownership admission is independent of witness/script fields. -/
private def sourceDeclarationJson (start : Nat) (declaration : SourceOperationDeclaration) : Json :=
  Json.mkObj [("name", Json.str declaration.name), ("role", Json.str declaration.role),
    ("agreement_profile", profileJson declaration.agreementProfile),
    ("progress_contract", Json.str declaration.progressContract),
    ("progress_window", Json.str declaration.progressWindow), ("budget_ticks", Json.num declaration.budgetTicks),
    ("requires_proof", Json.bool declaration.requiresProof),
    ("required_children", Json.arr (declaration.requiredChildren.map (fun child =>
      Json.mkObj [("pc", Json.num (child.pc - start : Nat)), ("call", callJson start child.call)])).toArray)]

private def sourceOutcomeJson : SourceOperationOutcome → Json
  | .success value => Json.mkObj [("kind", "success"), ("value", value.map valueToJson |>.getD Json.null)]
  | .failure value => Json.mkObj [("kind", "failure"), ("value", value.map valueToJson |>.getD Json.null)]
  | .timeout value => Json.mkObj [("kind", "timeout"), ("value", value.map valueToJson |>.getD Json.null)]
  | .cancelled => Json.mkObj [("kind", "cancelled")]

private def operationPhaseJson : OperationPhase → Json
  | .pending => "pending" | .blocked => "blocked" | .succeeded => "succeeded" | .failed => "failed"
  | .cancelled => "cancelled" | .timedOut => "timed_out" | .handedOff => "handed_off"
private def progressStateJson : ProgressState → Json
  | .pending => "pending" | .blocked => "blocked" | .noProgress => "no_progress" | .degraded => "degraded"
  | .succeeded => "succeeded" | .failed => "failed" | .cancelled => "cancelled"
  | .timedOut => "timed_out" | .handedOff => "handed_off"
private def sourceRecordJson (record : OperationInstance) : Json :=
  Json.mkObj [("agreement_profile", record.agreementProfile.map profileJson |>.getD Json.null),
    ("operation_id", Json.str record.operationId), ("session", optionalNat record.session),
    ("owner_id", record.ownerId.map Json.str |>.getD Json.null), ("kind", Json.str record.kind),
    ("phase", operationPhaseJson record.phase),
    ("handler_identity", record.handlerIdentity.map Json.str |>.getD Json.null),
    ("effect_ids", Json.arr (record.effectIds.map Json.num).toArray),
    ("dependent_operation_ids", Json.arr (record.dependentOperationIds.map Json.str).toArray),
    ("terminal_publication", record.terminalPublication.map Json.str |>.getD Json.null),
    ("budget_ticks", optionalNat record.budgetTicks), ("requires_proof", Json.bool record.requiresProof)]
private def sourceProgressJson (contract : ProgressContract) : Json :=
  Json.mkObj [("operation_id", Json.str contract.operationId), ("session", optionalNat contract.session),
    ("state", progressStateJson contract.state), ("last_ordering_key", optionalNat contract.lastOrderingKey),
    ("bounded", Json.bool contract.bounded), ("budget_ticks", optionalNat contract.budgetTicks),
    ("last_progress_tick", optionalNat contract.lastProgressTick),
    ("escalated_at_tick", optionalNat contract.escalatedAtTick),
    ("reason", contract.reason.map Json.str |>.getD Json.null)]

private def sourceOperationJson (st : State) (start : Nat)
    (coro : CoroutineState UnitGuard ScriptEffect) : Except String (Option Json) := do
  match coro.operationContinuation with
  | none => return none
  | some original =>
    if original.validationFailure.isSome then throw "source operation transition diagnostic outside supported comparison"
    let records := st.operationInstances.filter (fun record => record.operationId == original.operationId)
    let contracts := st.progressContracts.filter (fun contract => contract.operationId == original.operationId)
    let ([record], [contract]) := (records, contracts)
      | throw "source operation canonical records missing or ambiguous"
    let completed ← original.completedChildren.mapM (fun (id, outcome) => do
      let response ← nominalResponseJson outcome.response
      return Json.mkObj [("effect_id", Json.num id), ("status", statusJson outcome.status), ("response", response)])
    let failure ← match coro.operationFailure with
      | none => pure Json.null
      | some failure => faultJson (.faulted failure)
    return some (Json.mkObj [("coro_id", Json.num coro.id), ("role", Json.str coro.role),
      ("session", Json.num original.owner.sessionId), ("entry_pc", Json.num start),
      ("operation_id", Json.str original.operationId), ("owner", ownerJson original.owner),
      ("declaration", sourceDeclarationJson start original.declaration),
      ("original_pc", Json.num (original.originalPc - start : Nat)), ("runtime_original_pc", Json.num original.originalPc),
      ("issued_at", Json.num original.issuedAt), ("children", Json.arr (original.children.map Json.num).toArray),
      ("admitted_slots", Json.arr (original.admittedSlots.map (fun pc => Json.num (pc - start : Nat))).toArray),
      ("completed_children", Json.arr completed.toArray),
      ("outcome", original.outcome.map sourceOutcomeJson |>.getD Json.null),
      ("resolved", Json.bool original.resolved), ("invalidated", Json.bool original.invalidated),
      ("execution_failure", failure), ("record", sourceRecordJson record), ("progress", sourceProgressJson contract)])

private def admitReadinessOwner (st : State) (role ownerId : String) : Except String State := do
  let coro ← match st.coroutines.toList.find? (fun coro => coro.role == role) with
    | some coro => pure coro | none => throw "missing readiness owner coroutine"
  let endpoint ← match coro.ownedEndpoints.find? (fun endpoint => endpoint.role == role) with
    | some endpoint => pure endpoint | none => throw "missing original readiness endpoint"
  let (admitted, _) ← admitLoadedSessionOwner st endpoint.sid ownerId
  return admitted

/-- Only an actual canonical Blocked occurrence permits the between-round issuer. -/
private def issueAfterActualBlocked (st : State) (call : NominalCommandCall) : Except String State := do
  let coro ← match st.coroutines.toList.find? (fun coro => coro.role == call.role) with
    | some coro => pure coro | none => throw "missing readiness coroutine"
  if coro.effectCtx.readinessWitness.isSome then pure st else
  match coro.nominalContinuation with
  | none => pure st
  | some original => do
    if !(st.outstandingEffects.any (fun effect => effect.effectId == original.invocation && effect.status == .blocked)) then
      pure st
    else
      let endpoint ← match coro.ownedEndpoints.find? (fun endpoint => endpoint.role == call.role) with
        | some endpoint => pure endpoint | none => throw "missing original readiness endpoint"
      let session ← match st.sessions.lookup endpoint.sid with
        | some session => pure session | none => throw "missing original readiness session"
      let owner ← match original.originalOwner with
        | some owner => pure owner | none => throw "missing admitted original readiness owner"
      let predicate ← match call.declaration.readinessPredicate with
        | some predicate => pure predicate | none => throw "missing source readiness predicate"
      let (ownership, witness) ← session.ownership.issueReadiness owner predicate (some st.clock)
      pure { st with
        sessions := st.sessions.map (fun (sid, current) =>
          if sid == endpoint.sid then (sid, { current with ownership := ownership }) else (sid, current)),
        coroutines := st.coroutines.map (fun current => if current.id == coro.id then
          { current with effectCtx := { current.effectCtx with readinessWitness := some witness } } else current) }

private def runReadinessRounds (fuel : Nat) (st : State) (call : NominalCommandCall) : Except String State := do
  match fuel with
  | 0 => pure st
  | remaining + 1 =>
    let next := runScheduled 1 1 st
    let issued ← issueAfterActualBlocked next call
    if allTerminal issued then pure issued
    else if issued.sched.stepCount == st.sched.stepCount then pure issued
    else runReadinessRounds remaining issued call

/-- Run the original instruction image through the canonical loader and
scheduled execution. This function is dispatched by the existing runner. -/
def runNominalImage (payload : Json) : Except String Json := do
  if (← payload.getObjValAs? String "schema_version") != "nominal_image.v2" then
    throw "unsupported nominal executable image schema"
  let image ← parseImage (← payload.getObjVal? "image")
  let scripts ← parseScripts (← payload.getObjVal? "outcomes")
  let identity ← payload.getObjValAs? String "handler_identity"
  let rounds ← payload.getObjValAs? Nat "max_steps"
  let registers ← payload.getObjValAs? Nat "num_registers"
  let denyOutputs ← payload.getObjValAs? Bool "deny_outputs"
  if identity.isEmpty || rounds == 0 || registers == 0 || registers > 65535 then
    throw "unbound nominal machine configuration"
  let nominalRoles := image.program.code.toList.filterMap fun instruction => match instruction with
    | .invoke (.command call) => some call.role | _ => none
  if (scripts.map Prod.fst).length != nominalRoles.length ||
      !(nominalRoles.all fun role => (scripts.map Prod.fst).contains role) then
    throw "nominal provider roles do not match executable command roles"
  let initial := emptyState registers
  let initial : State := { initial with
    config := { initial.config with
    outputCondition :=
    { policy := if denyOutputs then .denyAll else .allowAll } } }
  let loaded ← match loadChoreographyResult initial image with
    | .ok st _ => pure st
    | .validationFailed reason => throw reason
    | _ => throw "nominal executable image capacity refusal"
  let loaded : State := { loaded with
    coroutines := loaded.coroutines.map fun coro =>
    { coro with effectCtx := { remaining := (scripts.lookup coro.role).getD [], identity := identity } } }
  let readiness := (payload.getObjVal? "readiness_admission").toOption
  let call ← match image.program.code.toList.filterMap (fun instruction => match instruction with
      | .invoke (.command call) => some call | _ => none) with
    | [call] => pure call | _ => throw "missing or ambiguous actual nominal command"
  let st ← match readiness, call.declaration.readinessPredicate with
    | none, none => do
      let admitted ← admitReadinessOwner loaded call.role "original"
      pure (runScheduled rounds 1 admitted)
    | some admission, some _ =>
      let ownerId ← admission.getObjValAs? String "owner_id"
      let afterBlocked ← admission.getObjValAs? Bool "issue_after_blocked"
      if ownerId.isEmpty || !afterBlocked then throw "readiness requires original owner and actual Blocked boundary"
      let admitted ← admitReadinessOwner loaded call.role ownerId
      runReadinessRounds rounds admitted call
    | _, _ => throw "readiness setup does not match the actual source declaration"
  let coroutines ← st.coroutines.toList.mapM fun coro => do
    let start := (image.program.entryPoints.lookup coro.role).getD 0
    let fault ← faultJson coro.status
    pure (Json.mkObj [("coro_id", Json.num coro.id), ("role", Json.str coro.role), ("pc", Json.num (coro.pc - start : Nat)),
      ("status", Json.str (coroStatus coro.status)), ("fault", fault),
      ("continuation", continuationJson start coro.nominalContinuation), ("exchange_count", Json.num ((st.effectExchanges.filter fun exchange =>
        match exchange.request.body with
        | .nominalCommand request => request.coroutine == coro.id | _ => false).length)),
      ("registers", Json.arr (coro.regs.map valueToJson))])
  let sourceOperations ← st.coroutines.toList.mapM (fun coro =>
    sourceOperationJson st ((image.program.entryPoints.lookup coro.role).getD 0) coro)
  let effects := (st.outstandingEffects.filter (fun effect => effect.effectKind == "nominal_command")).map fun effect => Json.mkObj [
    ("effect_id", Json.num effect.effectId), ("status", Json.str (effectStatus effect.status)),
    ("issued_at", ((st.effectExchanges.filterMap fun exchange => match exchange.request.body with
      | .nominalCommand request => if request.invocation == effect.effectId then some exchange.request.tick else none
      | _ => none).head?).map Json.num |>.getD Json.null),
    ("ordering_key", Json.num effect.orderingKey), ("completed_at_tick", optionalNat effect.completedAtTick),
    ("budget_ticks", optionalNat effect.budgetTicks)]
  let operations := (st.operationInstances.filter (fun operation =>
    st.outstandingEffects.any (fun effect => effect.effectKind == "nominal_command" && effect.operationId == operation.operationId))).map fun operation => Json.mkObj [
    ("effect_ids", Json.arr (operation.effectIds.map Json.num).toArray),
    ("kind", Json.str operation.kind), ("requires_proof", Json.bool operation.requiresProof),
    ("profile_name", operation.agreementProfile.map (fun profile => Json.str profile.profileName) |>.getD Json.null)]
  let events := st.obsTrace.filterMap fun event => match event.event with
    | .invoked endpoint (.command call) => some (Json.mkObj [
        ("tick", Json.num event.tick), ("session", Json.num endpoint.sid),
        ("role", Json.str call.role), ("interface", Json.str call.declaration.interfaceName),
        ("operation", Json.str call.declaration.operationName)])
    | _ => none
  let readinessView := match readiness with
    | none => Json.null
    | some _ => match st.coroutines.toList.find? (fun coro => coro.role == call.role) with
      | some coro => match coro.ownedEndpoints.find? (fun endpoint => endpoint.role == call.role) with
        | some endpoint => match st.sessions.lookup endpoint.sid with
          | some session => registryJson session.ownership | none => Json.null
        | none => Json.null
      | none => Json.null
  let exchanges ← st.effectExchanges.mapM exchangeJson
  pure (Json.mkObj [("schema_version", "nominal_image.v2"),
    ("coroutines", Json.arr coroutines.toArray), ("effects", Json.arr effects.toArray),
    ("operations", Json.arr operations.toArray),
    ("source_operations", Json.arr (sourceOperations.filterMap id).toArray),
    ("exchanges", Json.arr exchanges.toArray),
    ("invoked", Json.arr events.toArray), ("readiness", readinessView)])

end Runtime.Tests.NominalImageRunner
