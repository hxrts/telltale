import Lean.Data.Json
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Runtime.Loader
import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.ProtocolMachine.Runtime.Json
import Choreography.Projection.Json

/-! Executable-image operation of the existing protocol-machine runner.
The input contains actual bytecode and typed nominal outcomes. Communication
projections are validated but never regenerated into replacement bytecode. -/
set_option autoImplicit false
namespace Runtime.Tests.NominalImageRunner
open Lean (Json)
open Runtime.ProtocolMachine.Model
open Choreography.Projection.Json

inductive ScriptEffect : Type
inductive Action where
  | declaration (value : NominalCommandDeclaration)
  | command (value : NominalCommandCall)
  | operation (value : OperationAction)
  deriving DecidableEq
inductive HostOutcome where
  | success (result : Except String NominalCommandValue) (replyOffset : Nat)
  | readiness (replyOffset : Nat)
  | blocked
  | failure (kind message : String)
  | wrongResponse
structure Context where
  remaining : List HostOutcome := []
  calls : Nat := 0
  identity : String := "nominal.bridge"
  readinessWitness : Option SessionTypes.ReadinessWitness := none
  deriving Inhabited

instance : EffectRuntime ScriptEffect where
  EffectAction := Action
  EffectCtx := Context
  -- Classified actions never fall through to this generic path.
  exec := fun _ ctx => ctx
  commandDeclaration := fun action => match action with
    | .declaration value => some value | _ => none
  commandCall := fun action => match action with
    | .command value => some value | _ => none
  relocateCommand := fun action call => match action with
    | .command _ => some (.command call) | _ => none
  operationAction := fun action => match action with
    | .operation value => some value | _ => none
  relocateOperation := fun action operation => match action with
    | .operation _ => some (.operation operation) | _ => none
  commandHandlerIdentity := fun ctx => ctx.identity
  invokeCommand := fun _ request ctx =>
    let (outcome, rest) := match ctx.remaining with
      | [] => (EffectOutcome.mk (.failure "unavailable" "nominal provider script exhausted") none, [])
      | outcome :: rest =>
          let actual := match outcome with
            | .blocked => EffectOutcome.mk .blocked none
            | .failure kind message => EffectOutcome.mk (.failure kind message) none
            | .wrongResponse => EffectOutcome.mk .success (some .release)
            | .readiness offset => match ctx.readinessWitness with
              | none => EffectOutcome.mk (.failure "unavailable" "original readiness result has not been issued") none
              | some witness => EffectOutcome.mk .success
                  (some (.nominalCommand ⟨request.invocation + offset, .ok (.readiness witness)⟩))
            | .success result offset => EffectOutcome.mk .success
                (some (.nominalCommand ⟨request.invocation + offset, result⟩))
          (actual, rest)
    (outcome, { ctx with remaining := rest, calls := ctx.calls + 1 })
instance : Inhabited (EffectRuntime.EffectCtx ScriptEffect) := ⟨{}⟩
instance : EffectGuardBridge ScriptEffect UnitGuard where bridge := fun _ => ()
instance : PersistenceEffectBridge UnitPersist ScriptEffect where bridge := fun _ => ()

abbrev State := ProtocolMachineState UnitIdentity UnitGuard UnitPersist ScriptEffect UnitVerify

def config (registers : Nat) : ProtocolMachineConfig UnitIdentity UnitGuard UnitPersist ScriptEffect UnitVerify :=
  { bufferConfig := fun _ => unitBufferConfig, schedPolicy := .cooperative,
    violationPolicy := { allow := fun _ => false }, flowPolicy := unitFlowPolicy,
    spatialOk := fun _ => true, transportOk := fun _ _ => true,
    complianceProof := fun _ => ((), ()), numRegisters := registers,
    maxCoroutines := 1024, maxSessions := 256,
    monitorMode := .sessionTypePrecheck, guardChain := unitGuardChain,
    proofConfig := { guardChainWf := unitGuardChainWf }, roleSigningKey := fun _ => (),
    costModel := { stepCost := fun _ => 1, minCost := 1, defaultBudget := 18446744073709551615,
      hMinCost := by intro _ _; exact Nat.le_refl 1, hMinPos := by exact Nat.le_refl 1 },
    speculationEnabled := false }

def emptyState (registers : Nat) : State :=
  { config := config registers,
    code := { code := #[], entryPoints := [], localTypes := [], handlerTypes := [], metadata := ProgramMeta.empty },
    programs := #[], coroutines := #[], buffers := [], persistent := (), nextCoroId := 0,
    nextSessionId := 0, arena := { slots := #[], nextFree := 0, capacity := 0, inv := Nat.le_refl 0 },
    sessions := [], resourceStates := {}, guardResources := [],
    sched := { policy := .cooperative, readyQueue := [], blockedSet := {}, timeslice := 1, stepCount := 0 },
    monitor := { step := fun sk => some sk }, obsTrace := [], clock := 0,
    crashedSites := [], partitionedEdges := [], mask := (), ghostSessions := default, progressSupply := () }

def parseDeclaration (value : Json) : Except String NominalCommandDeclaration := do
  let interface ← value.getObjValAs? String "interface"
  let operation ← value.getObjValAs? String "operation"
  let mayBlock ← value.getObjValAs? Bool "may_block"
  let predicate ← match value.getObjVal? "readiness_predicate" with
    | .error _ => pure none
    | .ok .null => pure none
    | .ok field => pure (some (← field.getStr?))
  pure ⟨interface, operation, mayBlock, predicate⟩

def parseCall (value : Json) : Except String NominalCommandCall := do
  let declaration ← parseDeclaration (← value.getObjVal? "declaration")
  let profile ← value.getObjVal? "agreement_profile"
  let name ← profile.getObjValAs? String "profile_name"
  if (← profile.getObjValAs? String "visibility") != "immediate" ||
      (← profile.getObjValAs? String "rule") != "no_agreement" ||
      (← profile.getObjValAs? String "usable_at") != "none" ||
      (← profile.getObjValAs? String "finalized_at") != "none" ||
      (← profile.getObjValAs? String "required_evidence_kind") != "witness" then
    throw "unsupported selected nominal agreement profile"
  let operation ← value.getObjValAs? String "enclosing_operation"
  let role ← value.getObjValAs? String "role"
  let progress ← value.getObjValAs? String "progress_contract"
  let window ← value.getObjValAs? String "progress_window"
  let budget ← value.getObjValAs? Nat "budget_ticks"
  let result ← value.getObjValAs? Nat "result"
  let ok ← value.getObjValAs? Nat "on_ok"
  let err ← value.getObjValAs? Nat "on_err"
  if budget == 0 || budget > 18446744073709551615 then throw "invalid selected nominal tick budget"
  pure { declaration := declaration, enclosingOperation := operation,
    agreementProfile := ⟨name, .immediate, .noAgreement, .none, .none, .witness⟩,
    role := role, progressContract := progress, progressWindow := window,
    budgetTicks := budget, result := result, onOk := ok, onErr := err }

private def parseOperationDeclaration (value : Json) : Except String SourceOperationDeclaration := do
  let name ← value.getObjValAs? String "name"
  let role ← value.getObjValAs? String "role"
  let profile ← value.getObjVal? "agreement_profile"
  let profileName ← profile.getObjValAs? String "profile_name"
  if (← profile.getObjValAs? String "visibility") != "immediate" ||
      (← profile.getObjValAs? String "rule") != "no_agreement" ||
      (← profile.getObjValAs? String "usable_at") != "none" ||
      (← profile.getObjValAs? String "finalized_at") != "none" ||
      (← profile.getObjValAs? String "required_evidence_kind") != "witness" then
    throw "unsupported selected source operation agreement profile"
  let contract ← value.getObjValAs? String "progress_contract"
  let window ← value.getObjValAs? String "progress_window"
  let budget ← value.getObjValAs? Nat "budget_ticks"
  let proof ← value.getObjValAs? Bool "requires_proof"
  let children ← (← (← value.getObjVal? "required_children").getArr?).toList.mapM (fun child => do
    let pc ← child.getObjValAs? Nat "pc"
    let call ← parseCall (← child.getObjVal? "call")
    pure ({ pc, call } : DeclaredOperationChild))
  if budget == 0 || budget > 18446744073709551615 then throw "invalid original source operation budget"
  let declaration : SourceOperationDeclaration :=
    { name, role, agreementProfile := ⟨profileName, .immediate, .noAgreement, .none, .none, .witness⟩,
      progressContract := contract, progressWindow := window, budgetTicks := budget,
      requiresProof := proof, requiredChildren := children }
  if !declaration.supported then throw "unsupported original source operation declaration"
  return declaration

private def parseOperationResolution (value : Json) : Except String SourceOperationResolution := do
  if value = Json.str "Cancelled" then return .cancelled
  let fields ← value.getObj?
  if fields.toList.length != 1 then throw "ambiguous source operation resolution"
  let register := fun field => match field with
    | Json.null => Except.ok none
    | field => do
        let register ← field.getNat?
        if register > 65535 then throw "source resolution register out of range"
        return some register
  match fields.toList with
  | [("Success", field)] => return .success (← register field)
  | [("Failure", field)] => return .failure (← register field)
  | _ => throw "unsupported source operation resolution/escalation"

private def parseOperationAction (value : Json) : Except String OperationAction := do
  match ← value.getObjValAs? String "operation_lifecycle" with
  | "begin" => return .begin (← parseOperationDeclaration (← value.getObjVal? "declaration"))
  | "await" => return .await (← value.getObjValAs? String "operation")
  | "resolve" => return .resolve (← value.getObjValAs? String "operation")
      (← parseOperationResolution (← value.getObjVal? "outcome"))
  | "invalidate" => return .invalidate (← value.getObjValAs? String "operation")
  | _ => throw "unsupported actual source operation action"

def parseInstruction (value : Json) : Except String (Instr UnitGuard ScriptEffect) := do
  let fields ← value.getArr?
  match fields.toList with
  | [Json.str "declare", declaration] => pure (.invoke (.declaration (← parseDeclaration declaration)))
  | [Json.str "command", call] => pure (.invoke (.command (← parseCall call)))
  | [Json.str "operation", action] => pure (.invoke (.operation (← parseOperationAction action)))
  | [Json.str "offer", channel, label] => pure (.offer (← channel.getNat?) (← label.getStr?))
  | [Json.str "choose", channel, table] =>
      let entries ← table.getArr?
      let table ← entries.toList.mapM fun entry => do
        match (← entry.getArr?).toList with
        | [label, pc] => pure ((← label.getStr?), (← pc.getNat?))
        | _ => throw "invalid executable choice entry"
      pure (.choose (← channel.getNat?) table)
  | [Json.str "send", channel, source] => pure (.send (← channel.getNat?) (← source.getNat?))
  | [Json.str "receive", channel, destination] => pure (.receive (← channel.getNat?) (← destination.getNat?))
  | [Json.str "jump", target] => pure (.jump (← target.getNat?))
  | [Json.str "halt"] => pure .halt
  | _ => throw "unsupported executable instruction; communication recompilation is forbidden"

def parseImage (value : Json) : Except String (CodeImage UnitGuard ScriptEffect) := do
  let global ← globalTypeFromJson (← value.getObjVal? "global_type")
  let programs ← value.getObjValAs? (Array Json) "programs"
  let programs ← programs.toList.mapM fun entry => do
    match (← entry.getArr?).toList with
    | [role, code] =>
        let instructions ← code.getArr?
        pure ((← role.getStr?), (← instructions.toList.mapM parseInstruction).toArray)
    | _ => throw "invalid executable role program"
  let locals ← value.getObjValAs? (Array Json) "local_types"
  let locals ← locals.toList.mapM fun entry => do
    match (← entry.getArr?).toList with
    | [role, local] => pure ((← role.getStr?), (← localTypeRFromJson local))
    | _ => throw "invalid original role type"
  if (programs.map Prod.fst).eraseDups.length != programs.length ||
      (locals.map Prod.fst).eraseDups.length != locals.length then throw "duplicate executable role"
  if locals.length != programs.length ||
      !(locals.all fun entry => (programs.map Prod.fst).contains entry.1) then
    throw "executable/type role mismatch"
  let roles := programs.map Prod.fst
  let image : RoleCodeImage UnitGuard ScriptEffect :=
    { programs := programs.foldl (fun acc entry => acc.insert entry.1 entry.2) {},
      localTypes := locals.foldl (fun acc entry => acc.insert entry.1 entry.2) {}, globalType := global }
  let executable ← image.toCodeImage roles
  let calls := executable.program.code.toList.filter fun instruction => match instruction with
    | .invoke (.command _) => true | _ => false
  if calls.length != 1 then throw "nominal executable comparison requires one actual command instruction"
  pure executable

def parseOutcome (value : Json) : Except String HostOutcome := do
  let status ← value.getObjValAs? String "status"
  match status with
  | "blocked" => pure .blocked
  | "wrong_response" => pure .wrongResponse
  | "failure" =>
      let failure ← value.getObjVal? "failure"
      pure (.failure (← failure.getObjValAs? String "kind") (← failure.getObjValAs? String "message"))
  | "readiness" =>
      let offset ← value.getObjValAs? Nat "reply_offset"
      if offset > 1 then throw "unsupported nominal comparison reply offset"
      pure (.readiness offset)
  | "success" =>
      let result ← value.getObjVal? "result"
      let result ← match result.getObjValAs? Bool "Ok" with
        | .ok value => pure (.ok (.bool value))
        | .error _ => pure (.error (← result.getObjValAs? String "Err"))
      let offset ← value.getObjValAs? Nat "reply_offset"
      if offset > 1 then throw "unsupported nominal comparison reply offset"
      pure (.success result offset)
  | _ => throw "unknown nominal provider outcome"

def parseScripts (value : Json) : Except String (List (String × List HostOutcome)) := do
  let entries ← value.getArr?
  let scripts ← entries.toList.mapM fun entry => do
    match (← entry.getArr?).toList with
    | [role, outcomes] =>
        pure ((← role.getStr?), (← (← outcomes.getArr?).toList.mapM parseOutcome))
    | _ => throw "invalid nominal provider script"
  if (scripts.map Prod.fst).eraseDups.length != scripts.length then throw "duplicate nominal provider role"
  if scripts.any (fun entry => entry.2.isEmpty) then throw "missing typed nominal provider outcomes"
  pure scripts

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
    ("on_ok", Json.num (call.onOk - start)), ("on_err", Json.num (call.onErr - start))]
private def continuationJson (start : Nat) (holder : Option NominalCommandContinuation) : Json :=
  match holder with
  | none => Json.null
  | some original => Json.mkObj [("invocation", Json.num original.invocation),
      ("original_pc", Json.num (original.pc - start)), ("call", callJson start original.call),
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
      Json.mkObj [("pc", Json.num (child.pc - start)), ("call", callJson start child.call)])).toArray)]

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
      ("original_pc", Json.num (original.originalPc - start)), ("runtime_original_pc", Json.num original.originalPc),
      ("issued_at", Json.num original.issuedAt), ("children", Json.arr (original.children.map Json.num).toArray),
      ("admitted_slots", Json.arr (original.admittedSlots.map (fun pc => Json.num (pc - start))).toArray),
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
  let initial := { initial with config := { initial.config with outputCondition :=
    { policy := if denyOutputs then .denyAll else .allowAll } } }
  let loaded ← match loadChoreographyResult initial image with
    | .ok st _ => pure st
    | .validationFailed reason => throw reason
    | _ => throw "nominal executable image capacity refusal"
  let loaded := { loaded with coroutines := loaded.coroutines.map fun coro =>
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
    pure (Json.mkObj [("coro_id", Json.num coro.id), ("role", Json.str coro.role), ("pc", Json.num (coro.pc - start)),
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
