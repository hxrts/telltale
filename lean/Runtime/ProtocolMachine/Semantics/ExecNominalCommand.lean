import Runtime.ProtocolMachine.Semantics.ExecHelpers
import Runtime.ProtocolMachine.Semantics.ExecOperationLifecycle
import Runtime.ProtocolMachine.Model.SemanticObjects.OutstandingEffects

/-! Executable nominal protocol transaction. Canonical endpoint ownership is
checked here. Rust's additional issued host-owner/generation admission remains
under rust-host-owned-session-parity; this model does not mint a host handle. -/
set_option autoImplicit false
universe u
open Runtime.ProtocolMachine.Model

private def nominalSupportedProfile (call : NominalCommandCall) : Bool :=
  decide (call.agreementProfile.profileName ≠ "" ∧
    call.agreementProfile.visibility = .immediate ∧
    call.agreementProfile.rule = .noAgreement ∧
    call.agreementProfile.usableAt = .none ∧
    call.agreementProfile.finalizedAt = .none ∧
    call.agreementProfile.requiredEvidenceKind = .witness)

private def nominalProgram {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) : Program γ ε :=
  (st.programs[coro.programId]?).getD st.code

private def nominalDeclared {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (call : NominalCommandCall) : Bool :=
  let program := nominalProgram st coro
  match program.entryPoints.find? (fun entry => entry.1 == coro.role) with
  | none => false
  | some entry =>
      let limit := program.entryPoints.foldl (fun stop other =>
        if entry.2 < other.2 then min stop other.2 else stop) program.code.size
      decide (entry.2 ≤ coro.pc ∧ coro.pc < limit ∧ call.role = coro.role) &&
        ((program.code.toList.drop entry.2).take (coro.pc - entry.2)).any
          (fun instruction => match instruction with
            | .invoke action => decide (EffectRuntime.commandDeclaration action = some call.declaration)
            | _ => false)

private def nominalEndpoint? {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) (call : NominalCommandCall) : Option Endpoint :=
  coro.ownedEndpoints.find? (fun endpoint => endpoint.role == call.role)

private def nominalValidCall {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (call : NominalCommandCall) : Bool :=
  let code := (nominalProgram st coro).code
  let terminal := fun target => nominalTerminalBranch code code.size target call.enclosingOperation
  call.declaration.readinessWellFormed && nominalProgramValid (nominalProgram st coro) &&
    nominalSupportedProfile call && nominalDeclared st coro call &&
    decide (call.declaration.interfaceName ≠ "" ∧ call.declaration.operationName ≠ "" ∧
      call.enclosingOperation ≠ "" ∧ call.progressContract ≠ "" ∧ call.progressWindow ≠ "" ∧
      call.budgetTicks > 0 ∧ call.result > 0 ∧ call.result < coro.regs.size ∧
      call.onOk > coro.pc ∧ call.onErr > coro.pc ∧ call.onOk ≠ call.onErr) &&
    terminal call.onOk && terminal call.onErr

private def nominalSessionActive {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (endpoint : Endpoint) : Bool :=
  match st.sessions.lookup endpoint.sid with
  | none => false
  | some session => match session.phase with
    | .active => decide (endpoint ∈ session.endpoints)
    | _ => false

private def nominalOriginalOwnerValid {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (original : NominalCommandContinuation) : Bool :=
  match original.originalOwner, nominalEndpoint? coro original.call with
  | some owner, some endpoint => match st.sessions.lookup endpoint.sid with
    | some session => decide (coro.issuedModelOwner = some owner) &&
        owner.sessionId == endpoint.sid && session.ownership.admits owner
    | none => false
  | _, _ => false

private def nominalOriginalValid {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (call : NominalCommandCall) (original : NominalCommandContinuation) : Bool :=
  match nominalEndpoint? coro call,
      st.outstandingEffects.find? (fun effect => effect.effectId == original.invocation),
      st.operationInstances.find? (fun operation => operation.operationId == s!"effect:{original.invocation}") with
  | some endpoint, some effect, some operation =>
      nominalSessionActive st endpoint && decide (original.coroutine = coro.id ∧ original.pc = coro.pc ∧ original.call = call ∧
        effect.operationId = operation.operationId ∧ effect.session = some endpoint.sid ∧ effect.ownerId = original.originalOwner.map (fun owner => owner.ownerId) ∧ effect.orderingKey = original.issuedAt ∧
        effect.budgetTicks = some call.budgetTicks ∧
        (effect.status = .pending ∨ effect.status = .blocked) ∧
        effect.handlerIdentity = original.handlerIdentity ∧
        operation.kind = call.enclosingOperation ∧ operation.agreementProfile = some call.agreementProfile ∧
        operation.budgetTicks = some call.budgetTicks ∧ operation.requiresProof = true) &&
      nominalOriginalOwnerValid st coro original &&
      sourceOperationChildContextValid st coro call &&
      original.withinOriginalWindowAt st.clock &&
      (EffectRuntime.commandHandlerIdentity coro.effectCtx == original.handlerIdentity)
  | _, _, _ => false

private def issueNominal {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (call : NominalCommandCall) (endpoint : Endpoint) :
    ProtocolMachineState ι γ π ε ν × CoroutineState γ ε :=
  let id := st.nextEffectId
  let operationId := s!"effect:{id}"
  let handler := EffectRuntime.commandHandlerIdentity coro.effectCtx
  let original : NominalCommandContinuation :=
    { invocation := id, coroutine := coro.id, pc := coro.pc, call := call,
      issuedAt := st.clock, returned := none, handlerIdentity := handler,
      originalOwner := coro.issuedModelOwner }
  let effect : OutstandingEffect :=
    { effectId := id, operationId := operationId, session := some endpoint.sid,
      ownerId := original.originalOwner.map (fun owner => owner.ownerId), effectInterface := some call.declaration.interfaceName,
      effectOperation := some call.declaration.operationName, effectKind := "nominal_command",
      handlerIdentity := handler, status := .pending, orderingKey := st.clock,
      budgetTicks := some call.budgetTicks, retryPolicy := "forbid_late_results",
      invalidationToken := s!"effect:{id}:original", completedAtTick := none,
      inputs := "typed nominal command", outputs := "pending" }
  let operation : OperationInstance :=
    { operationId := operationId, agreementProfile := some call.agreementProfile,
      session := some endpoint.sid, ownerId := original.originalOwner.map (fun owner => owner.ownerId), kind := call.enclosingOperation,
      phase := .pending, handlerIdentity := some handler, effectIds := [id],
      dependentOperationIds := [], terminalPublication := none,
      budgetTicks := some call.budgetTicks, requiresProof := true }
  let progress : ProgressContract :=
    { operationId := operationId, session := some endpoint.sid, state := .pending,
      lastOrderingKey := some st.clock, bounded := true, budgetTicks := some call.budgetTicks,
      lastProgressTick := some st.clock, escalatedAtTick := none, reason := none }
  ({ st with nextEffectId := id + 1,
      outstandingEffects := st.outstandingEffects ++ [effect],
      operationInstances := st.operationInstances ++ [operation],
      progressContracts := st.progressContracts ++ [progress] },
    { coro with nominalContinuation := some original })

private def settleNominal {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (original : NominalCommandContinuation)
    (status : OutstandingEffectStatus) (output : String) : ProtocolMachineState ι γ π ε ν :=
  let terminal := decide (status ≠ .pending ∧ status ≠ .blocked)
  let phase : OperationPhase := match status with
    | .succeeded => .succeeded | .blocked => .blocked | .pending => .pending
    | .cancelled => .cancelled | .invalidated => .timedOut | .failed => .failed
  let progress : ProgressState := match status with
    | .succeeded => .succeeded | .blocked => .blocked | .pending => .pending
    | .cancelled => .cancelled | .invalidated => .timedOut | .failed => .failed
  let operationId := s!"effect:{original.invocation}"
  { st with
    outstandingEffects := st.outstandingEffects.map fun effect =>
      if effect.effectId == original.invocation then
        { effect with status := status, outputs := output,
          completedAtTick := if terminal then some st.clock else effect.completedAtTick }
      else effect,
    operationInstances := st.operationInstances.map fun operation =>
      if operation.operationId == operationId then
        { operation with phase := phase,
          terminalPublication := if status = .succeeded then some "effect.succeeded" else operation.terminalPublication }
      else operation,
    progressContracts := st.progressContracts.map fun contract =>
      if contract.operationId == operationId then
        { contract with state := progress }
      else contract }

private def consumeNominalReadiness {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (original : NominalCommandContinuation) (result : Except String NominalCommandValue) :
    ProtocolMachineState ι γ π ε ν × Except String Unit :=
  match result with
  | .error _ => (st, .ok ())
  | .ok value =>
    if !value.matchesDeclaration original.call.declaration then
      (st, .error "nominal result does not match its declared readiness predicate/type")
    else match value with
    | .bool _ => (st, .ok ())
    | .readiness witness =>
      match original.originalOwner, nominalEndpoint? coro original.call with
      | some owner, some endpoint => match st.sessions.lookup endpoint.sid with
        | none => (st, .error "missing original readiness session")
        | some session =>
          if owner.sessionId != endpoint.sid then (st, .error "readiness owner belongs to another session")
          else
            let (ownership, result) := session.ownership.attemptConsumeReadiness owner witness (some st.clock)
            ({ st with sessions := st.sessions.map (fun (sid, current) =>
              if sid == endpoint.sid then (sid, { current with ownership := ownership }) else (sid, current)) }, result)
      | _, _ => (st, .error "missing original readiness owner or endpoint")

/-- Consume the original typed result after the existing output gate. -/
def commitNominalCommand {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (pack' : StepPack ι γ π ε ν) : StepPack ι γ π ε ν :=
  if !pack'.nominalCommit then pack' else
  match pack'.coro.nominalContinuation with
  | none => faultPack pack'.st pack'.coro (.effectFault "contract_violation" "missing original nominal continuation") "missing original nominal continuation"
  | some original =>
      if !nominalOriginalValid pack'.st pack'.coro original.call original then
        faultPack pack'.st pack'.coro (.effectFault "contract_violation" "original nominal continuation is no longer admissible") "inadmissible continuation"
      else match original.returned with
      | none => faultPack pack'.st pack'.coro (.effectFault "contract_violation" "nominal result is still pending") "pending result"
      | some result =>
          let (target, value) := match result with
            | .ok value => (original.call.onOk, value.toValue)
            | .error reason => (original.call.onErr, Value.string reason)
          if h : original.call.result < pack'.coro.regs.size then
            let (consumed, admission) := consumeNominalReadiness pack'.st pack'.coro original result
            match admission with
            | .error reason => faultPack consumed pack'.coro (.effectFault "contract_violation" reason) reason
            | .ok () =>
              let coro := { pack'.coro with
                regs := pack'.coro.regs.set (i := original.call.result) (v := value) (h := h),
                pc := target, status := .ready, nominalContinuation := none }
              let st := settleNominal consumed original .succeeded "typed application result"
              { pack' with coro := coro, st := st, nominalCommit := false }
          else faultPack pack'.st pack'.coro .outOfRegisters "result register missing"

private def nominalRequest (original : NominalCommandContinuation)
    (request : NominalCommandRequest) : EffectRequest :=
  { effectId := some original.invocation, tick := original.issuedAt,
    session := some request.session, operationId := some s!"effect:{original.invocation}",
    metadata := { interfaceName := request.declaration.interfaceName,
      operationName := request.declaration.operationName, authorityClass := if request.declaration.readinessPredicate.isSome then .authoritative else .command,
      semanticClass := if request.declaration.readinessPredicate.isSome then .authoritative else .bestEffort, admissibility := .declaredUseOnly,
      totality := if request.declaration.mayBlock then .mayBlock else .mustTerminate,
      timeoutPolicy := if request.declaration.mayBlock then .required (some original.call.budgetTicks) else .none,
      retryShape := .forbidden, reentrancyPolicy := .allow, handlerDomain := .external },
    body := .nominalCommand request }

/-- Execute the same original nominal protocol occurrence. No generic exec fallback. -/
def stepNominalCommand {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (action : EffectRuntime.EffectAction ε) (call : NominalCommandCall) : StepPack ι γ π ε ν :=
  if !nominalValidCall st coro call || !sourceOperationChildContextValid st coro call then
    faultPack st coro (.effectFault "contract_violation" "unsupported or undeclared nominal call") "invalid nominal call"
  else match nominalEndpoint? coro call with
  | none => faultPack st coro (.effectFault "contract_violation" "nominal role endpoint is not owned") "unowned endpoint"
  | some endpoint =>
      match st.sessions.lookup endpoint.sid with
      | none => faultPack st coro (.effectFault "contract_violation" "nominal session is missing") "missing session"
      | some session =>
          if !nominalSessionActive st endpoint || session.handlers.isEmpty then faultPack st coro (.effectFault "contract_violation" "no handler bound") "no handler bound" else
          let originalOwnerAdmitted := match coro.issuedModelOwner with
            | none => false
            | some owner => owner.sessionId == endpoint.sid && session.ownership.admits owner
          if coro.nominalContinuation.isNone && !originalOwnerAdmitted then
            faultPack st coro (.effectFault "contract_violation"
              "nominal invocation requires original admitted coroutine ownership") "unowned nominal invocation"
          else
            let admission := match coro.nominalContinuation with
              | none =>
                  let (issued, resident) := issueNominal st coro call endpoint
                  attachSourceOperationChild issued resident call st.nextEffectId
              | some _ => Except.ok (st, coro)
            match admission with
            | .error reason => faultPack st coro (.effectFault "contract_violation" reason) reason
            | .ok (issued, resident) =>
              match resident.nominalContinuation with
              | none => faultPack issued resident (.effectFault "contract_violation" "nominal issuance failed") "issuance failed"
              | some original =>
                  if !nominalOriginalValid issued resident call original then
                    faultPack issued resident (.effectFault "contract_violation" "original nominal window or occurrence refused") "original occurrence refused"
                  else
                    let finish := fun (current : ProtocolMachineState ι γ π ε ν) (resident : CoroutineState γ ε) =>
                      { (pack resident current (mkRes .continue (some (.obs (.invoked endpoint action))))) with nominalCommit := true }
                    match original.returned with
                    | some _ => finish issued resident
                    | none =>
                        let request : NominalCommandRequest :=
                          ⟨original.invocation, endpoint.sid, resident.id, call.declaration, call.role⟩
                        let (outcome, context) := EffectRuntime.invokeCommand action request resident.effectCtx
                        let resident := retainSourceOperationOutcome
                          { resident with effectCtx := context } original.invocation outcome
                        let issued := { issued with effectExchanges := issued.effectExchanges ++
                          [{ effectId := original.invocation, handlerIdentity := original.handlerIdentity,
                            orderingKey := original.issuedAt, request := nominalRequest original request,
                            outcome := outcome, observedAt := some issued.clock }] }
                        -- Retain the genuine typed result before an independent
                        -- post-callback refusal; never invoke the callback again.
                        let accepted := outcome.acceptedStatusFor (.nominalCommand request)
                        let returned := match accepted, outcome.response with
                          | .success, some (.nominalCommand reply) => { original with returned := some reply.result }
                          | _, _ => original
                        let resident := { resident with nominalContinuation := some returned }
                        if !nominalOriginalValid issued resident call returned then
                          let refused := { returned with validationFailure := some
                            ("contract_violation", "original occurrence refused after callback") }
                          let resident := { resident with nominalContinuation := some refused }
                          let (primaryKind, primary) := match accepted with
                            | .failure kind message => (kind, message)
                            | _ => ("contract_violation", "original occurrence refused after callback")
                          let failed := settleNominal issued original .failed primary
                          faultPack failed resident (.effectFault primaryKind primary) primary
                        else match accepted with
                        | .failure kind message =>
                            let failed := settleNominal issued original .failed s!"{kind}:{message}"
                            faultPack failed resident (.effectFault kind message) message
                        | .blocked =>
                            if !call.declaration.mayBlock then
                              let failed := settleNominal issued original .failed "immediate command returned Blocked"
                              faultPack failed resident (.effectFault "contract_violation" "immediate command returned Blocked") "blocked immediate command"
                            else
                              -- Preserve the original ordering key and progress window.
                              let blocked := settleNominal issued original .blocked "blocked"
                              pack { resident with status := .ready } blocked (mkRes .continue none)
                        | .success =>
                            match outcome.response with
                            | some (.nominalCommand _) => finish issued resident
                            | _ => faultPack issued resident (.effectFault "contract_violation" "malformed nominal outcome") "malformed outcome"

/-! ## Executable nominal correspondence facts
These facts concern this protocol transition and the canonical semantic fields.
They do not establish Rust host-owner issuance, physical cleanup, or a complete
source-compiler refinement theorem. -/

/-- The continuation's admission endpoint is precisely the existing outstanding
operation model's inclusive logical-tick endpoint. No progress escalation or
retry constructs a new window. -/
theorem nominalOriginalWindow_iff (original : NominalCommandContinuation) (tick : Nat) :
    original.withinOriginalWindowAt tick = true ↔
      tick ≤ original.issuedAt + original.call.budgetTicks := by
  simp [NominalCommandContinuation.withinOriginalWindowAt]

/-- Every settlement transition preserves the original ordering keys. In
particular a Blocked observation cannot refresh the issued tick. -/
theorem settleNominal_preserves_ordering {ι γ π ε ν : Type u}
    [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (original : NominalCommandContinuation)
    (status : OutstandingEffectStatus) (output : String) :
    ((settleNominal st original status output).outstandingEffects.map
      (fun effect => effect.orderingKey)) =
        st.outstandingEffects.map (fun effect => effect.orderingKey) := by
  simp only [settleNominal, List.map_map]
  congr 1
  funext effect
  simp only [Function.comp_apply]
  split <;> rfl

/-- A genuine staged result commits the typed branch only under the actual
canonical admissibility check. The declaration itself is not an authority
premise and generic `exec` is not invoked by this transition. -/
theorem commitNominalCommand_typed_branch {ι γ π ε ν : Type u}
    [ProtocolMachineDomain ι γ π ε ν]
    (pack' : StepPack ι γ π ε ν) (original : NominalCommandContinuation)
    (result : Except String NominalCommandValue)
    (commit : pack'.nominalCommit = true)
    (resident : pack'.coro.nominalContinuation = some original)
    (admitted : nominalOriginalValid pack'.st pack'.coro original.call original = true)
    (returned : original.returned = some result)
    (destination : original.call.result < pack'.coro.regs.size)
    (consumedState : ProtocolMachineState ι γ π ε ν)
    (consumed : consumeNominalReadiness pack'.st pack'.coro original result = (consumedState, .ok ())) :
    (commitNominalCommand pack').coro.pc =
      (match result with | .ok _ => original.call.onOk | .error _ => original.call.onErr) := by
  cases result <;>
    simp [commitNominalCommand, commit, resident, admitted, returned, destination, consumed]
