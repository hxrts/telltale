import Runtime.Tests.OperationReadinessExecution

/-! Actual central commit refusal and original parent revocation. Semantic
invalidation here is not host-future settlement or a physical cleanup receipt. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Runtime.Tests.OperationFailureExecution
open Runtime.ProtocolMachine.Model
open Runtime.Tests.NominalCommandExecution
open Runtime.Tests.OperationReadinessExecution

private def outputFaultRetained (st : State) : Bool :=
  st.coroutines[1]?.any (fun coro =>
    match coro.status, coro.operationFailure with
    | .faulted (.outputCondition current), some (.outputCondition original) => current == original
    | _, _ => false)

/-- Both states come from actual installed opcodes, original owner claim, real
readiness issuance and output-condition denial in commitPack. -/
def originalOutputRefusal : Bool := (do
  let before ← jointBlocked
  let after ← jointResumed false
  let previous ← before.coroutines[1]?
  let current ← after.coroutines[1]?
  let original ← previous.operationContinuation
  let revoked ← current.operationContinuation
  let parent ← after.operationInstances.find? (fun row => row.operationId == original.operationId)
  let progress ← after.progressContracts.find? (fun row => row.operationId == original.operationId)
  let child ← after.outstandingEffects.find? (fun row => original.children.contains row.effectId)
  let reobserved := (execAtPC after current.id current).1
  return outputFaultRetained after && outputFaultRetained reobserved &&
    revoked.invalidated && !revoked.resolved && revoked.outcome.isNone &&
    decide (revoked.owner = original.owner) &&
    decide (revoked.declaration = original.declaration) &&
    revoked.issuedAt == original.issuedAt && revoked.originalPc == original.originalPc &&
    revoked.children == original.children && revoked.completedChildren.length == 1 &&
    parent.phase == .failed && parent.effectIds == original.children &&
    parent.terminalPublication.isNone && progress.state == .failed &&
    progress.lastOrderingKey == some original.issuedAt &&
    progress.budgetTicks == some original.declaration.budgetTicks &&
    child.status == .invalidated && child.completedAtTick == some 1 &&
    current.nominalContinuation.any (fun nominal => nominal.returned.isSome) &&
    after.sessions.all (fun entry => entry.2.ownership.consumedWitnesses.isEmpty)
  ).getD false

example output_refusal_retains_original_fault_and_revokes_only_original_semantic_work :
    originalOutputRefusal = true := by decide

/-- The expired original Await executes its actual installed opcode. Its fault
enters the central owner; no child or replacement endpoint is synthesized. -/
def originalExpiryRefusal : Bool := (do
  let before ← Runtime.Tests.OperationLifecycleExecution.sourceBegun
  let previous ← before.coroutines[1]?
  let original ← previous.operationContinuation
  let after ← invokeInstalled { before with clock := 6 } 1
  let current ← after.coroutines[1]?
  let revoked ← current.operationContinuation
  let parent ← after.operationInstances.find? (fun row => row.operationId == original.operationId)
  return revoked.invalidated && !revoked.resolved &&
    revoked.issuedAt == original.issuedAt && decide (revoked.owner = original.owner) &&
    revoked.declaration.budgetTicks == original.declaration.budgetTicks &&
    parent.phase == .failed && after.outstandingEffects.isEmpty &&
    (match current.status, current.operationFailure with
      | .faulted (.effectFault kind message), some (.effectFault originalKind originalMessage) =>
          kind == originalKind && message == originalMessage
      | _, _ => false)
  ).getD false

example expired_original_await_retains_first_fault_without_renewal_or_cleanup_ack :
    originalExpiryRefusal = true := by decide

/-- A genuine installed Jump bypasses a still-present static Resolve. Runtime
Halt must refuse rather than treating static presence as actual resolution. -/
def originalHaltRefusal : Bool := (do
  let declaration := Runtime.Tests.OperationLifecycleExecution.sourceDeclaration
  let roles := Runtime.Tests.OperationLifecycleExecution.sourceRoleImage
  let roles := { roles with
    programs := roles.programs.insert "A"
    #[.invoke (.operation (.begin declaration)), .jump 3,
      .invoke (.operation (.resolve "Save" (.success none))), .halt] }
  let image ← (roles.toCodeImage ["B", "A"]).toOption
  let loaded ← match loadChoreographyResult empty image with
    | .ok st _ => some st | _ => none
  let initial ← loaded.coroutines[1]?
  let endpoint ← initial.ownedEndpoints.head?
  let (admitted, _) ← (admitLoadedSessionOwner loaded endpoint.sid "original-owner").toOption
  let begun ← invokeInstalled admitted 1
  let beforeJump ← begun.coroutines[1]?
  let jumped := (execAtPC begun beforeJump.id beforeJump).1
  let beforeHalt ← jumped.coroutines[1]?
  let refused := (execAtPC jumped beforeHalt.id beforeHalt).1
  let current ← refused.coroutines[1]?
  let original ← current.operationContinuation
  return original.invalidated && !original.resolved && original.children.isEmpty &&
    refused.operationInstances.any (fun parent => parent.operationId == original.operationId && parent.phase == .failed) &&
    (match current.status, current.operationFailure with
      | .faulted (.effectFault kind message), some (.effectFault originalKind originalMessage) =>
          kind == originalKind && message == originalMessage
      | _, _ => false)
  ).getD false

example actual_jump_cannot_halt_without_original_terminal_resolution :
    originalHaltRefusal = true := by decide

end Runtime.Tests.OperationFailureExecution
