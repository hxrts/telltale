import Runtime.Tests.NominalCommandExecution

/-! Actual installed source-operation actions, separate from child effect:id
operations. These declarations exercise canonical model owner admission and
application resolution, not physical Rust capabilities or proof publication. -/
set_option autoImplicit false
namespace Runtime.Tests.OperationLifecycleExecution
open Runtime.ProtocolMachine.Model
open Runtime.Tests.NominalCommandExecution

def sourceDeclaration : SourceOperationDeclaration :=
  { name := "Save", role := "A", agreementProfile := call.agreementProfile,
    progressContract := "original-progress", progressWindow := "original-window",
    budgetTicks := 5, requiresProof := true }

def sourceRoleImage : RoleCodeImage UnitGuard TestEffect :=
  { programs := ({} : Std.HashMap Role (Bytecode UnitGuard TestEffect))
      |>.insert "A" #[.invoke (.operation (.begin sourceDeclaration)),
        .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.success none))), .halt]
      |>.insert "B" #[.halt],
    localTypes := ({} : Std.HashMap Role SessionTypes.LocalTypeR.LocalTypeR)
      |>.insert "A" .end |>.insert "B" .end,
    globalType := .end }

/-- Claim is an actual canonical model transition on the loaded session.
No witness/serialized capability fields are used to recreate the owner. -/
def sourceLoaded (claimOwner : Bool) : Option State := do
  let executable ← (sourceRoleImage.toCodeImage ["B", "A"]).toOption
  let st ← match loadChoreographyResult empty executable with
    | .ok st _ => some st
    | _ => none
  if !claimOwner then return st
  let coro ← st.coroutines[1]?
  let endpoint ← coro.ownedEndpoints.head?
  let (admitted, _) ← (admitLoadedSessionOwner st endpoint.sid "original-owner").toOption
  return admitted

def sourceBegun : Option State := do
  let st ← sourceLoaded true
  invokeInstalled st 1

def sourceResolved : Option State := do
  let begun ← sourceBegun
  let awaited ← invokeInstalled begun 1
  invokeInstalled awaited 1

example : (sourceBegun.map fun st =>
    st.nextEffectId == 0 && st.operationInstances.length == 1 &&
      st.progressContracts.length == 1 && st.outstandingEffects.isEmpty &&
      st.coroutines[1]?.any (fun coro => coro.effectCtx.genericCalls == 0 &&
        coro.effectCtx.calls == 0 && coro.operationContinuation.isSome)).getD false = true := by
  simp [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, sourceDeclaration, sourceRoleImage,
    sourceLoaded, sourceBegun, sourceResolved] <;> decide

example : (sourceResolved.map fun st =>
    st.operationInstances.any (fun operation => decide (operation.phase = .succeeded) &&
      operation.requiresProof && operation.terminalPublication.isNone) &&
    st.coroutines[1]?.any (fun coro => coro.operationContinuation.any (fun original =>
      original.resolved && original.issuedAt == 0 && original.children.isEmpty))).getD false = true := by
  simp [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, sourceDeclaration, sourceRoleImage,
    sourceLoaded, sourceBegun, sourceResolved] <;> decide

/-- Ordinary loading alone does not authorize the installed source action. -/
example : ((sourceLoaded false).bind (fun st => invokeInstalled st 1) |>.map fun st =>
    st.operationInstances.isEmpty && st.outstandingEffects.isEmpty &&
      st.coroutines[1]?.any (fun coro => coro.effectCtx.calls == 0 &&
        match coro.status with | .faulted _ => true | _ => false)).getD false = true := by
  simp [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, sourceDeclaration, sourceRoleImage,
    sourceLoaded, sourceBegun, sourceResolved] <;> decide

/-- Inclusive original endpoint succeeds; a later tick refuses without issuing
another occurrence or resetting its original window. -/
example : (sourceBegun.bind fun st => invokeInstalled { st with clock := 5 } 1 |>.map fun st =>
    st.coroutines[1]?.any (fun coro => match coro.status with | .ready => true | _ => false)).getD false = true := by
  simp [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, sourceDeclaration, sourceRoleImage,
    sourceLoaded, sourceBegun, sourceResolved] <;> decide

example : (sourceBegun.bind fun st => invokeInstalled { st with clock := 6 } 1 |>.map fun st =>
    st.operationInstances.length == 1 && st.coroutines[1]?.any (fun coro =>
      coro.operationContinuation.any (fun original => original.issuedAt == 0) &&
      match coro.status with | .faulted _ => true | _ => false)).getD false = true := by
  simp [
    image, roleImage, empty, ordinaryLoaded,
    loaded, invokeInstalled, blocked, resumed,
    prepared, readinessPrepared, RoleCodeImage.toCodeImage, CodeImage.toRoleCodeImage,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, sourceDeclaration, sourceRoleImage,
    sourceLoaded, sourceBegun, sourceResolved] <;> decide

end Runtime.Tests.OperationLifecycleExecution
