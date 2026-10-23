import Runtime.ProtocolMachine.Semantics.ExecHelpers
import Runtime.ProtocolMachine.Model.OperationLifecycle

/-! The source operation transaction uses the existing canonical coroutine,
operation/progress fields, session authority and scheduler status. Revocation
changes protocol commit admissibility, never physical host resource custody. -/
set_option autoImplicit false
universe u
open Runtime.ProtocolMachine.Model

private def sourceOperationSession {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (sid : Nat) : Bool :=
  coro.ownedEndpoints.any (fun endpoint => endpoint.sid == sid && endpoint.role == coro.role) &&
  match st.sessions.lookup sid with
  | none => false
  | some session => match session.phase with
    | .active => true
    | _ => false

private def sourceOperationBegin {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (declaration : SourceOperationDeclaration) : StepPack ι γ π ε ν := Id.run do
  let refuse := fun message => faultPack st coro (.effectFault "contract_violation" message) message
  if !declaration.supported || declaration.role != coro.role then
    return refuse "source operation declaration is not applicable to this role"
  if coro.operationContinuation.any (fun original => !original.resolved && !original.invalidated) then
    return refuse "original source operation is still live"
  let some endpoint := coro.ownedEndpoints.find? (fun endpoint => endpoint.role == coro.role)
    | return refuse "source operation has no actual endpoint"
  let some session := st.sessions.lookup endpoint.sid
    | return refuse "source operation session is absent"
  let some owner := coro.issuedModelOwner
    | return refuse "source operation requires original admitted coroutine ownership"
  if owner.sessionId != endpoint.sid || !session.ownership.admits owner ||
      !sourceOperationSession st coro endpoint.sid then
    return refuse "source operation owner/session is not currently admitted"
  let (original, record, progress) := OriginalOperationContinuation.begin owner declaration coro.id coro.pc st.clock
  if st.operationInstances.any (fun current => current.operationId == record.operationId) ||
      st.progressContracts.any (fun current => current.operationId == record.operationId) then
    return refuse "duplicate original source operation occurrence"
  let issued := { st with
    operationInstances := st.operationInstances ++ [record],
    progressContracts := st.progressContracts ++ [progress] }
  return continuePack issued { coro with operationContinuation := some original, operationFailure := none } none

private def sourceOperationResolution {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) (resolution : SourceOperationResolution) :
    Except String SourceOperationOutcome := do
  let read := fun register => match register with
    | none => Except.ok none
    | some register => match coro.regs[register]? with
      | none => Except.error "source operation resolution register is absent"
      | some value => Except.ok (some value)
  match resolution with
  | .success register => return .success (← read register)
  | .failure register => return .failure (← read register)
  | .timeout _ => throw "timeout resolution requires actual original escalation lowering"
  | .cancelled => return .cancelled

private def sourceOperationProgress : OperationPhase → ProgressState
  | .pending => .pending
  | .blocked => .blocked
  | .succeeded => .succeeded
  | .failed => .failed
  | .cancelled => .cancelled
  | .timedOut => .timedOut
  | .handedOff => .handedOff

private def settleSourceOperation {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (original : OriginalOperationContinuation)
    (phase : OperationPhase) : ProtocolMachineState ι γ π ε ν :=
  { st with
    operationInstances := st.operationInstances.map (fun record =>
      if record.operationId == original.operationId then { record with phase } else record),
    progressContracts := st.progressContracts.map (fun contract =>
      if contract.operationId == original.operationId then
        { contract with
          state := sourceOperationProgress phase,
          lastProgressTick := if phase = .succeeded ∨ phase = .failed ∨ phase = .timedOut ∨ phase = .cancelled then
            some st.clock else contract.lastProgressTick } else contract) }

private def invalidateSourceOperation {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (original : OriginalOperationContinuation) :
    ProtocolMachineState ι γ π ε ν :=
  let failed := { st with
    operationInstances := st.operationInstances.map (fun record =>
      if record.operationId == original.operationId then { record with phase := .failed } else record),
    progressContracts := st.progressContracts.map (fun contract =>
      if contract.operationId == original.operationId then
        { contract with state := .failed, reason := some "explicit original operation invalidation" }
      else contract) }
  { failed with
    outstandingEffects := failed.outstandingEffects.map (fun effect =>
      if original.children.contains effect.effectId &&
          (effect.status == .pending || effect.status == .blocked) then
        { effect with status := .invalidated, completedAtTick := some st.clock }
      else effect) }

private def advanceSourceOperation {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (original : OriginalOperationContinuation) (action : OperationAction) : StepPack ι γ π ε ν :=
  let refuse := fun message => faultPack st coro (.effectFault "contract_violation" message) message
  match action with
  | .await _ => match original.observeChildren st.outstandingEffects with
    | .error message => refuse message
    | .ok .pending =>
        blockPack (settleSourceOperation st original .blocked) coro (.operationAwait original.operationId)
    | .ok .ready => continuePack st coro none
    | .ok (.failed kind message) => faultPack st coro (.effectFault kind message) message
  | .resolve _ resolution => match sourceOperationResolution coro resolution with
    | .error message => refuse message
    | .ok outcome =>
        if original.outcome.any (fun retained => decide (retained ≠ outcome)) then
          refuse "cannot replace original proposed source operation outcome"
        else
          let retained := { original with outcome := some outcome }
          let staged := { coro with operationContinuation := some retained }
          match retained.observeChildren st.outstandingEffects with
          | .error message => faultPack st staged (.effectFault "contract_violation" message) message
          | .ok .pending => faultPack st staged (.effectFault "contract_violation" "source children still live") "source children still live"
          | .ok (.failed kind message) =>
              match outcome with
              | .success _ => faultPack st staged (.effectFault kind message) message
              | _ => continuePack (settleSourceOperation st retained (OriginalOperationContinuation.resolutionPhase outcome))
                  { staged with operationContinuation := some { retained with resolved := true } } none
          | .ok .ready =>
              continuePack (settleSourceOperation st retained (OriginalOperationContinuation.resolutionPhase outcome))
                { staged with operationContinuation := some { retained with resolved := true } } none
  | .invalidate _ =>
      if original.children.any (fun id =>
          (st.outstandingEffects.filter (fun effect => effect.effectId == id &&
            effect.session == some original.owner.sessionId &&
            effect.ownerId == some original.owner.ownerId)).length != 1) then
        refuse "missing, foreign or ambiguous original child during invalidation"
      else continuePack (invalidateSourceOperation st original)
        { coro with operationContinuation := some { original with invalidated := true } } none
  | _ => refuse "invalid source operation continuation action"

/-- A real source action cannot fall through to generic host execution. -/
def stepOperationLifecycle {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (action : OperationAction) : StepPack ι γ π ε ν := Id.run do
  if let .begin declaration := action then return sourceOperationBegin st coro declaration
  let refuse := fun message => faultPack st coro (.effectFault "contract_violation" message) message
  let some original := coro.operationContinuation
    | return refuse "no original begun source operation continuation"
  let name := match action with
    | .await name | .resolve name _ | .invalidate name => some name
    | _ => none
  if name != some original.declaration.name || coro.role != original.declaration.role ||
      !sourceOperationSession st coro original.owner.sessionId then
    return refuse "source operation action does not identify original role/session"
  let some session := st.sessions.lookup original.owner.sessionId
    | return refuse "source operation original session is absent"
  let records := st.operationInstances.filter (fun record => record.operationId == original.operationId)
  let contracts := st.progressContracts.filter (fun contract => contract.operationId == original.operationId)
  let ([record], [contract]) := (records, contracts)
    | return refuse "source operation/progress missing or ambiguous"
  let applicable := match action with
    | .invalidate _ => original.identityValid session.ownership record contract
    | _ => original.admissibleAt session.ownership record contract st.clock
  if !applicable then return refuse "source operation owner/window/canonical records refused"
  return advanceSourceOperation st coro original action

/-- The actual installed source marker requires its original live continuation;
merely jumping over Begin cannot turn a required child into a legacy call. -/
def sourceOperationChildContextValid {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (call : NominalCommandCall) : Bool :=
  let program := (st.programs[coro.programId]?).getD st.code
  let required := (program.code.toList.take coro.pc).any (fun instruction =>
    match instruction with
    | .invoke action => match EffectRuntime.operationAction action with
      | some (.begin declaration) => declaration.name == call.enclosingOperation
      | _ => false
    | _ => false)
  match coro.operationContinuation with
  | none => !required
  | some original =>
      if original.resolved then !required
      else match st.sessions.lookup original.owner.sessionId with
      | none => false
      | some session =>
          let records := st.operationInstances.filter (fun record => record.operationId == original.operationId)
          let contracts := st.progressContracts.filter (fun contract => contract.operationId == original.operationId)
          match records, contracts with
          | [record], [contract] =>
              decide (coro.issuedModelOwner = some original.owner ∧ coro.role = original.declaration.role ∧
                original.declaration.name = call.enclosingOperation) &&
                sourceOperationSession st coro original.owner.sessionId &&
                original.admissibleAt session.ownership record contract st.clock &&
                original.declaration.requiredChildren.any (fun slot => decide (slot.pc = coro.pc ∧ slot.call = call))
          | _, _ => false

/-- Attach the original issued child, not a fresh descriptor or a lookup by
singleton membership (the enclosing operation can share that membership). -/
def attachSourceOperationChild {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (call : NominalCommandCall) (id : Nat) :
    Except String (ProtocolMachineState ι γ π ε ν × CoroutineState γ ε) := do
  match coro.operationContinuation with
  | none => return (st, coro)
  | some original =>
      if original.resolved then return (st, coro)
      if !sourceOperationChildContextValid st coro call then
        throw "source child lost original owner/continuation/window"
      let child ← match st.outstandingEffects.filter (fun effect => effect.effectId == id) with
        | [child] => .ok child
        | _ => .error "original issued source child absent or ambiguous"
      let attached ← original.admitChild coro.pc call child
      let issued := { st with
        operationInstances := st.operationInstances.map (fun record =>
          if record.operationId == original.operationId then
            { record with
              effectIds := attached.children,
              dependentOperationIds := record.dependentOperationIds ++ [child.operationId] }
          else record) }
      return (issued, { coro with operationContinuation := some attached })

/-- Retain the actual child outcome on the same original holder before any
post-callback validation can refuse its result. This is not callback cleanup. -/
def retainSourceOperationOutcome {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) (id : Nat) (outcome : EffectOutcome) : CoroutineState γ ε :=
  match coro.operationContinuation with
  | none => coro
  | some original =>
      if original.resolved || !original.children.contains id then coro
      else match outcome.status with
      | .blocked => coro
      | _ => match original.retainChildOutcome id outcome with
        | .ok retained => { coro with operationContinuation := some retained }
        | .error reason =>
            { coro with
              operationContinuation := some
              { original with validationFailure := original.validationFailure.or (some reason) } }

/-- Existing scheduler unblocking observes the same original child set. It never
polls a callback, reissues a child, or creates a new progress endpoint. -/
def sourceOperationAwaitShouldWake {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (id : String) : Bool :=
  match coro.operationContinuation with
  | none => true
  | some original =>
      if original.operationId != id || original.resolved || original.invalidated ||
          !original.withinOriginalWindowAt st.clock then true
      else match st.sessions.lookup original.owner.sessionId with
      | none => true
      | some session =>
          if !session.ownership.admits original.owner || coro.issuedModelOwner != some original.owner then true
          else match original.observeChildren st.outstandingEffects with
          | .ok .pending => false
          | _ => true


/-- Preserve the first actual typed execution fault on the canonical coroutine
and revoke only protocol commit authority of the same original parent/children.
No physical host settlement is inferred from this semantic invalidation. -/
def retainSourceOperationFailure {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (pack' : StepPack ι γ π ε ν) : StepPack ι γ π ε ν :=
  match pack'.coro.status, pack'.coro.operationContinuation with
  | .faulted fault, some original =>
      if original.resolved || original.invalidated then pack'
      else
        let st := { pack'.st with
          operationInstances := pack'.st.operationInstances.map (fun record =>
            if record.operationId == original.operationId &&
                (record.phase == .pending || record.phase == .blocked) then
              { record with phase := .failed } else record),
          progressContracts := pack'.st.progressContracts.map (fun contract =>
            if contract.operationId == original.operationId then
              { contract with
                state := match contract.state with
                  | .succeeded | .failed | .cancelled | .timedOut | .handedOff => contract.state
                  | _ => .failed,
                reason := some "original source operation execution failed" }
            else contract),
          outstandingEffects := pack'.st.outstandingEffects.map (fun effect =>
            if original.children.contains effect.effectId &&
                (effect.status == .pending || effect.status == .blocked) then
              { effect with status := .invalidated, completedAtTick := some pack'.st.clock }
            else effect) }
        { pack' with
            st, coro := { pack'.coro with
            operationContinuation := some { original with invalidated := true },
            operationFailure := pack'.coro.operationFailure.or (some fault) } }
  | _, _ => pack'
