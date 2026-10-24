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

/-! Exact producer normal forms. They enter execution proofs only through the
actual assembler, checked loader and complete owner-admission equations below. -/
def sourceStageImage (jumpToHalt : Bool) : CodeImage UnitGuard TestEffect :=
  { program := {
      code := #[.halt, .invoke (.operation (.begin sourceDeclaration)),
        if jumpToHalt then .jump 4 else .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.success none))), .halt],
      entryPoints := [("B", 0), ("A", 1)],
      localTypes := [("B", .end_), ("A", .end_)],
      localTypesR := [("B", .end), ("A", .end)],
      handlerTypes := [], metadata := ProgramMeta.empty }, globalType := .end }

def sourceStageCoroutine (role : String) (id pc : Nat) : CoroutineState UnitGuard TestEffect :=
  let endpoint : Endpoint := { sid := 0, role }
  { id, programId := 0, role, pc,
    regs := (Array.replicate Runtime.Tests.NominalCommandExecution.config.numRegisters .unit).set! 0 (.chan endpoint),
    status := .ready, effectCtx := default, ownedEndpoints := [endpoint],
    progressTokens := [], knowledgeSet := [], costBudget := 100, specState := none }

def sourceStageSession : SessionState UnitVerify :=
  { scope := { id := 0 }, sid := 0, roles := ["B", "A"],
    endpoints := [{ sid := 0, role := "B" }, { sid := 0, role := "A" }],
    localTypes := [({ sid := 0, role := "B" }, .end_), ({ sid := 0, role := "A" }, .end_)],
    traces := initDEnv 0 ["B", "A"], buffers := [], handlers := [], epoch := 0, phase := .active }

def sourceStageInstalled (jumpToHalt : Bool) : State :=
  { Runtime.Tests.NominalCommandExecution.empty with
    programs := #[(sourceStageImage jumpToHalt).program],
    coroutines := #[sourceStageCoroutine "B" 0 0, sourceStageCoroutine "A" 1 1],
    sessions := [(0, sourceStageSession)],
    sched := { Runtime.Tests.NominalCommandExecution.empty.sched with readyQueue := [0, 1] },
    obsTrace := [{ tick := 0, event := .opened 0 ["B", "A"] }],
    nextCoroId := 2, nextSessionId := 1 }

def sourceStageOwner : SessionTypes.ModelOwner := ⟨0, "original-owner", 0, .session⟩

def sourceStageOwned (jumpToHalt : Bool) : State :=
  let installed := sourceStageInstalled jumpToHalt
  { installed with
    sessions := [(0, { sourceStageSession with ownership := { current := some sourceStageOwner } })],
    coroutines := #[{ sourceStageCoroutine "B" 0 0 with issuedModelOwner := some sourceStageOwner },
      { sourceStageCoroutine "A" 1 1 with issuedModelOwner := some sourceStageOwner }] }

theorem source_stage_image_eq :
    sourceRoleImage.toCodeImage ["B", "A"] = .ok (sourceStageImage false) := by
  simp +decide only [sourceRoleImage, sourceStageImage, sourceDeclaration,
    RoleCodeImage.toCodeImage, mapExecutableTargets?, OperationAction.mapTargets?,
    EffectRuntime.operationAction, EffectRuntime.relocateOperation,
    EffectRuntime.commandDeclaration, EffectRuntime.commandCall, EffectRuntime.relocateCommand,
    Std.HashMap.size_insert, Std.HashMap.size_empty, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty, Std.HashMap.mem_insert, Std.HashMap.not_mem_empty,
    List.foldlM_cons, List.foldlM_nil, List.mapM, List.mapM.loop,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Option.bind,
    Array.isEmpty, Array.size, Nat.reduceAdd, List.nil_append, List.cons_append,
    List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, decide_true, decide_false, ↓reduceIte, ↓reduceDIte]

theorem source_stage_load_eq (jumpToHalt : Bool) :
    loadChoreographyResult Runtime.Tests.NominalCommandExecution.empty (sourceStageImage jumpToHalt) =
      .ok (sourceStageInstalled jumpToHalt) 0 := by
  cases jumpToHalt <;> simp +decide only [loadChoreographyResult, validateImage_eq,
    sourceStageImage, sourceDeclaration, Runtime.Tests.NominalCommandExecution.empty, Runtime.Tests.NominalCommandExecution.config,
    Choreography.Projection.Project.projectR?, Choreography.Projection.Project.trans,
    Choreography.Projection.Trans.trans, Choreography.Projection.Trans.transBranches,
    Choreography.Projection.Projectb.projectb, Choreography.Projection.Projectb.projectbBranches,
    localTypeRToLocalType, localTypeRToLocalTypeAux, localTypeRBranchesToChoices,
    List.find?_cons, List.find?_nil, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Except.toOption, Option.map, Option.bind,
    decide_true, decide_false, nextFreshSessionId, sessionIdAvailable, existingSessionIds,
    ↓reduceIte, ↓reduceDIte]
  all_goals
    apply congrArg (fun state : State => ChoreographyLoadResult.ok state 0)
    rfl

theorem source_stage_admission_eq (jumpToHalt : Bool) :
    admitLoadedSessionOwner (sourceStageInstalled jumpToHalt) 0 "original-owner" =
      .ok (sourceStageOwned jumpToHalt, sourceStageOwner) := by
  simp only [admitLoadedSessionOwner, sourceStageInstalled, sourceStageSession,
    sourceStageCoroutine, sourceStageOwned, sourceStageOwner, List.lookup, List.filter,
    List.any, List.isEmpty, List.map_cons, List.map_nil, Array.toList,
    List.map_toArray, beq_self_eq_true, SessionTypes.ModelOwnershipState.claim,
    Bind.bind, Pure.pure, Except.bind, Except.pure,
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  all_goals rfl

theorem source_stage_coro_eq (jumpToHalt : Bool) :
    (sourceStageInstalled jumpToHalt).coroutines[1]? = some (sourceStageCoroutine "A" 1 1) := rfl

theorem source_stage_endpoint_eq :
    (sourceStageCoroutine "A" 1 1).ownedEndpoints.head? = some ({ sid := 0, role := "A" } : Endpoint) := rfl

theorem source_loaded_eq (claimOwner : Bool) :
    sourceLoaded claimOwner = some (if claimOwner then sourceStageOwned false else sourceStageInstalled false) := by
  cases claimOwner <;>
    simp only [sourceLoaded, source_stage_image_eq, source_stage_load_eq,
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Bool.not_false, Bool.not_true,
      ↓reduceIte, source_stage_coro_eq, source_stage_endpoint_eq, source_stage_admission_eq]

theorem source_halt_image_eq :
    ({ sourceRoleImage with programs := sourceRoleImage.programs.insert "A"
      #[.invoke (.operation (.begin sourceDeclaration)), .jump 3,
        .invoke (.operation (.resolve "Save" (.success none))), .halt] } :
      RoleCodeImage UnitGuard TestEffect).toCodeImage ["B", "A"] =
      .ok (sourceStageImage true) := by
  simp +decide only [sourceRoleImage, sourceStageImage, sourceDeclaration,
    RoleCodeImage.toCodeImage, mapExecutableTargets?, OperationAction.mapTargets?,
    EffectRuntime.operationAction, EffectRuntime.relocateOperation,
    EffectRuntime.commandDeclaration, EffectRuntime.commandCall, EffectRuntime.relocateCommand,
    Std.HashMap.size_insert, Std.HashMap.size_empty, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty, Std.HashMap.mem_insert, Std.HashMap.not_mem_empty,
    List.foldlM_cons, List.foldlM_nil, List.mapM, List.mapM.loop,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Option.bind,
    Array.isEmpty, Array.size, Nat.reduceAdd, List.nil_append, List.cons_append,
    List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, decide_true, decide_false, ↓reduceIte, ↓reduceDIte]

example : (sourceBegun.map fun st =>
    st.nextEffectId == 0 && st.operationInstances.length == 1 &&
      st.progressContracts.length == 1 && st.outstandingEffects.isEmpty &&
      st.coroutines[1]?.any (fun coro => coro.effectCtx.genericCalls == 0 &&
        coro.effectCtx.calls == 0 && coro.operationContinuation.isSome)).getD false = true := by
  simp only [sourceBegun, sourceResolved, source_loaded_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      
      invokeInstalled, 
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

example : (sourceResolved.map fun st =>
    st.operationInstances.any (fun operation => decide (operation.phase = .succeeded) &&
      operation.requiresProof && operation.terminalPublication.isNone) &&
    st.coroutines[1]?.any (fun coro => coro.operationContinuation.any (fun original =>
      original.resolved && original.issuedAt == 0 && original.children.isEmpty))).getD false = true := by
  simp only [sourceBegun, sourceResolved, source_loaded_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      
      invokeInstalled, 
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

/-- Ordinary loading alone does not authorize the installed source action. -/
example : ((sourceLoaded false).bind (fun st => invokeInstalled st 1) |>.map fun st =>
    st.operationInstances.isEmpty && st.outstandingEffects.isEmpty &&
      st.coroutines[1]?.any (fun coro => coro.effectCtx.calls == 0 &&
        match coro.status with | .faulted _ => true | _ => false)).getD false = true := by
  simp only [sourceBegun, sourceResolved, source_loaded_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      
      invokeInstalled, 
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

/-- Inclusive original endpoint succeeds; a later tick refuses without issuing
another occurrence or resetting its original window. -/
example : (sourceBegun.bind fun st => invokeInstalled { st with clock := 5 } 1 |>.map fun st =>
    st.coroutines[1]?.any (fun coro => match coro.status with | .ready => true | _ => false)).getD false = true := by
  simp only [sourceBegun, sourceResolved, source_loaded_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      
      invokeInstalled, 
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

example : (sourceBegun.bind fun st => invokeInstalled { st with clock := 6 } 1 |>.map fun st =>
    st.operationInstances.length == 1 && st.coroutines[1]?.any (fun coro =>
      coro.operationContinuation.any (fun original => original.issuedAt == 0) &&
      match coro.status with | .faulted _ => true | _ => false)).getD false = true := by
  simp only [sourceBegun, sourceResolved, source_loaded_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      
      invokeInstalled, 
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

end Runtime.Tests.OperationLifecycleExecution
