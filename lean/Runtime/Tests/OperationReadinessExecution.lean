import Runtime.Tests.OperationLifecycleExecution

/-! Joint original-parent/readiness-child transaction. These are actual checked
role-image/installed-opcode declarations, not physical host-resource proofs. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Runtime.Tests.OperationReadinessExecution
open Runtime.ProtocolMachine.Model
open Runtime.Tests.NominalCommandExecution

def readinessDeclaration : NominalCommandDeclaration :=
  { declaration with readinessPredicate := some "Store.save" }
def readinessCall : NominalCommandCall :=
  { call with
    declaration := readinessDeclaration, enclosingOperation := "Save",
    onOk := 3, onErr := 7 }
def parentDeclaration : SourceOperationDeclaration :=
  { Runtime.Tests.OperationLifecycleExecution.sourceDeclaration with
    requiredChildren := [{ pc := 2, call := readinessCall }] }
def jointRoleImage : RoleCodeImage UnitGuard TestEffect :=
  { roleImage with
    programs := ({} : Std.HashMap Role (Bytecode UnitGuard TestEffect))
      |>.insert "A" #[.invoke (.declaration readinessDeclaration),
        .invoke (.operation (.begin parentDeclaration)), .invoke (.command readinessCall),
        .offer 0 "Ready", .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.success none))), .halt,
        .offer 0 "Denied", .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.failure none))), .halt]
      |>.insert "B" #[.choose 0 [("Ready", 1), ("Denied", 1)], .halt] }

def jointBlocked : Option State := do
  let image ← (jointRoleImage.toCodeImage ["B", "A"]).toOption
  let st ← match loadChoreographyResult empty image with | .ok st _ => some st | _ => none
  let coro ← st.coroutines[1]?
  let endpoint ← coro.ownedEndpoints.head?
  let (st, _) ← (admitLoadedSessionOwner st endpoint.sid "original-owner").toOption
  let st ← invokeInstalled st 1
  let st ← invokeInstalled st 1
  invokeInstalled st 1

def jointResumed (allowOutput : Bool) : Option State := do
  let st ← jointBlocked
  let coro ← st.coroutines[1]?
  let endpoint ← coro.ownedEndpoints.head?
  let session ← st.sessions.lookup endpoint.sid
  let owner ← coro.issuedModelOwner
  let (ownership, witness) ← (session.ownership.issueReadiness owner "Store.save" (some 1)).toOption
  let st := { st with
    clock := 1,
    config := { st.config with outputCondition := { verify := fun _ => allowOutput } },
    sessions := st.sessions.map (fun entry => if entry.1 == endpoint.sid then
      (entry.1, { entry.2 with ownership }) else entry),
    coroutines := st.coroutines.set! 1 { coro with effectCtx := { coro.effectCtx with readiness := some witness } } }
  invokeInstalled st 1

def offerInstalled (st : State) (index : Nat) : Option State := do
  let coro ← st.coroutines[index]?
  let program ← st.programs[coro.programId]?
  match program.code[coro.pc]? with
  | some (.offer channel label) => pure (commitPack st coro.id (stepOffer st coro channel label)).1
  | _ => none

def jointSettled : Option State := do
  let st ← jointResumed true
  let st ← offerInstalled st 1
  let st ← invokeInstalled st 1
  invokeInstalled st 1

theorem original_parent_owns_exact_blocked_readiness_child :
    (jointBlocked.map fun st =>
      st.coroutines[1]?.any (fun coro =>
        coro.effectCtx.calls == 1 && coro.nominalContinuation.isSome &&
        coro.operationContinuation.any (fun original => original.children.length == 1)) &&
      st.outstandingEffects.any (fun effect => effect.status == .blocked &&
        effect.orderingKey == 0 && effect.completedAtTick.isNone) &&
      st.operationInstances.length == 2).getD false = true := by
  simp only [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty, Std.HashMap.size_empty,
    Std.HashMap.mem_insert, Std.HashMap.not_mem_empty, List.foldlM_cons, List.foldlM_nil,
    Runtime.Tests.OperationLifecycleExecution.sourceDeclaration, Runtime.Tests.OperationLifecycleExecution.sourceRoleImage, Runtime.Tests.OperationLifecycleExecution.sourceLoaded, Runtime.Tests.OperationLifecycleExecution.sourceBegun,
    Runtime.Tests.OperationLifecycleExecution.sourceResolved, readinessDeclaration, readinessCall, parentDeclaration,
    jointRoleImage, jointBlocked, jointResumed, offerInstalled,
    jointSettled] <;> decide

theorem original_parent_resolves_after_actual_readiness_consumption :
    (jointSettled.map fun st =>
      st.coroutines[1]?.any (fun coro =>
        coro.effectCtx.calls == 2 && coro.nominalContinuation.isNone &&
        coro.operationContinuation.any (fun original => original.resolved && original.children.length == 1)) &&
      st.outstandingEffects.any (fun effect => effect.status == .succeeded &&
        effect.orderingKey == 0 && effect.completedAtTick == some 1) &&
      st.sessions.any (fun entry => entry.2.ownership.consumedWitnesses == [1]) &&
      st.operationInstances.all (fun operation => operation.phase == .succeeded)).getD false = true := by
  simp only [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty, Std.HashMap.size_empty,
    Std.HashMap.mem_insert, Std.HashMap.not_mem_empty, List.foldlM_cons, List.foldlM_nil,
    Runtime.Tests.OperationLifecycleExecution.sourceDeclaration, Runtime.Tests.OperationLifecycleExecution.sourceRoleImage, Runtime.Tests.OperationLifecycleExecution.sourceLoaded, Runtime.Tests.OperationLifecycleExecution.sourceBegun,
    Runtime.Tests.OperationLifecycleExecution.sourceResolved, readinessDeclaration, readinessCall, parentDeclaration,
    jointRoleImage, jointBlocked, jointResumed, offerInstalled,
    jointSettled] <;> decide

theorem output_refusal_cannot_spend_witness_or_resolve_original_parent :
    ((jointResumed false).map fun st =>
      st.coroutines[1]?.any (fun coro =>
        coro.effectCtx.calls == 2 && coro.nominalContinuation.any (fun original => original.returned.isSome) &&
        coro.operationContinuation.any (fun original => !original.resolved) &&
        (match coro.status with | .faulted _ => true | _ => false)) &&
      st.sessions.all (fun entry => entry.2.ownership.consumedWitnesses.isEmpty) &&
      !st.operationInstances.any (fun operation => operation.phase == .succeeded)).getD false = true := by
  simp only [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty, Std.HashMap.size_empty,
    Std.HashMap.mem_insert, Std.HashMap.not_mem_empty, List.foldlM_cons, List.foldlM_nil,
    Runtime.Tests.OperationLifecycleExecution.sourceDeclaration, Runtime.Tests.OperationLifecycleExecution.sourceRoleImage, Runtime.Tests.OperationLifecycleExecution.sourceLoaded, Runtime.Tests.OperationLifecycleExecution.sourceBegun,
    Runtime.Tests.OperationLifecycleExecution.sourceResolved, readinessDeclaration, readinessCall, parentDeclaration,
    jointRoleImage, jointBlocked, jointResumed, offerInstalled,
    jointSettled] <;> decide

end Runtime.Tests.OperationReadinessExecution
