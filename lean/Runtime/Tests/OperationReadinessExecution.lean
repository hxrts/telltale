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
    declaration := readinessDeclaration,
    enclosingOperation := Runtime.Tests.OperationLifecycleExecution.sourceDeclaration.name,
    role := Runtime.Tests.OperationLifecycleExecution.sourceDeclaration.role,
    agreementProfile := Runtime.Tests.OperationLifecycleExecution.sourceDeclaration.agreementProfile,
    progressContract := Runtime.Tests.OperationLifecycleExecution.sourceDeclaration.progressContract,
    progressWindow := Runtime.Tests.OperationLifecycleExecution.sourceDeclaration.progressWindow,
    budgetTicks := Runtime.Tests.OperationLifecycleExecution.sourceDeclaration.budgetTicks,
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

/-- The old never-admitted parent5/child2 fixture, retained as a rejection control.
Both the required manifest and installed child carry that SAME malformed call. -/
def malformedJointCall : NominalCommandCall :=
  { readinessCall with budgetTicks := call.budgetTicks }
def malformedJointParent : SourceOperationDeclaration :=
  { parentDeclaration with requiredChildren := [{ pc := 2, call := malformedJointCall }] }
def malformedJointRoleImage : RoleCodeImage UnitGuard TestEffect :=
  { jointRoleImage with
    programs := (jointRoleImage.programs.insert "A" #[.invoke (.declaration readinessDeclaration),
      .invoke (.operation (.begin malformedJointParent)), .invoke (.command malformedJointCall),
      .offer 0 "Ready", .invoke (.operation (.await "Save")),
      .invoke (.operation (.resolve "Save" (.success none))), .halt,
      .offer 0 "Denied", .invoke (.operation (.await "Save")),
      .invoke (.operation (.resolve "Save" (.failure none))), .halt]) }

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

/-! Producer stages for THIS joint declaration and relocated child image. -/
def jointStageCall : NominalCommandCall := { readinessCall with onOk := 5, onErr := 9 }
def jointStageDeclaration : SourceOperationDeclaration :=
  { parentDeclaration with requiredChildren := [{ pc := 4, call := jointStageCall }] }

def jointStageImage : CodeImage UnitGuard TestEffect :=
  let branches := [({ name := "Ready" }, none, SessionTypes.LocalTypeR.LocalTypeR.end),
    ({ name := "Denied" }, none, SessionTypes.LocalTypeR.LocalTypeR.end)]
  { program := {
      code := #[.choose 0 [("Ready", 1), ("Denied", 1)], .halt,
        .invoke (.declaration readinessDeclaration), .invoke (.operation (.begin jointStageDeclaration)),
        .invoke (.command jointStageCall), .offer 0 "Ready", .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.success none))), .halt,
        .offer 0 "Denied", .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.failure none))), .halt],
      entryPoints := [("B", 0), ("A", 2)],
      localTypes := [("B", .branch "A" [("Ready", .end_), ("Denied", .end_)]),
        ("A", .select "B" [("Ready", .end_), ("Denied", .end_)])],
      localTypesR := [("B", .recv "A" branches), ("A", .send "B" branches)],
      handlerTypes := [], metadata := ProgramMeta.empty }, globalType := global }

def malformedJointStageCall : NominalCommandCall :=
  { jointStageCall with budgetTicks := call.budgetTicks }
def malformedJointStageDeclaration : SourceOperationDeclaration :=
  { jointStageDeclaration with requiredChildren := [{ pc := 4, call := malformedJointStageCall }] }
def malformedJointStageImage : CodeImage UnitGuard TestEffect :=
  { jointStageImage with
    program := { jointStageImage.program with
      code := #[.choose 0 [("Ready", 1), ("Denied", 1)], .halt,
        .invoke (.declaration readinessDeclaration), .invoke (.operation (.begin malformedJointStageDeclaration)),
        .invoke (.command malformedJointStageCall), .offer 0 "Ready", .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.success none))), .halt,
        .offer 0 "Denied", .invoke (.operation (.await "Save")),
        .invoke (.operation (.resolve "Save" (.failure none))), .halt] } }

def jointStageCoroutine (role : String) (id pc : Nat) : CoroutineState UnitGuard TestEffect :=
  let endpoint : Endpoint := { sid := 0, role }
  { id, programId := 0, role, pc,
    regs := (Array.replicate Runtime.Tests.NominalCommandExecution.config.numRegisters .unit).set! 0 (.chan endpoint),
    status := .ready, effectCtx := default, ownedEndpoints := [endpoint],
    progressTokens := [], knowledgeSet := [], costBudget := 100, specState := none }

def jointStageSession : SessionState UnitVerify :=
  let edge : Edge := { sid := 0, sender := "A", receiver := "B" }
  { scope := { id := 0 }, sid := 0, roles := ["B", "A"],
    endpoints := [{ sid := 0, role := "B" }, { sid := 0, role := "A" }],
    localTypes := jointStageImage.program.localTypes.map
      (fun entry => ({ sid := 0, role := entry.1 }, entry.2)),
    traces := initDEnv 0 ["B", "A"], buffers := [(edge, [])],
    handlers := [(edge, 0)], epoch := 0, phase := .active }

def jointStageInstalled : State :=
  let edge : Edge := { sid := 0, sender := "A", receiver := "B" }
  { Runtime.Tests.NominalCommandExecution.empty with
    programs := #[jointStageImage.program],
    coroutines := #[jointStageCoroutine "B" 0 0, jointStageCoroutine "A" 1 2],
    buffers := [(edge, [])], sessions := [(0, jointStageSession)],
    sched := { Runtime.Tests.NominalCommandExecution.empty.sched with readyQueue := [0, 1] },
    obsTrace := [{ tick := 0, event := .opened 0 ["B", "A"] }],
    nextCoroId := 2, nextSessionId := 1 }

def jointStageOwner : SessionTypes.ModelOwner := ⟨0, "original-owner", 0, .session⟩
def jointStageOwned : State :=
  { jointStageInstalled with
    sessions := [(0, { jointStageSession with ownership := { current := some jointStageOwner } })],
    coroutines := #[{ jointStageCoroutine "B" 0 0 with issuedModelOwner := some jointStageOwner },
      { jointStageCoroutine "A" 1 2 with issuedModelOwner := some jointStageOwner }] }

theorem joint_stage_image_eq :
    jointRoleImage.toCodeImage ["B", "A"] = .ok jointStageImage := by
  simp +decide only [jointRoleImage, jointStageImage, jointStageCall, jointStageDeclaration,
    parentDeclaration, readinessCall, readinessDeclaration, roleImage, declaration, call, global,
    Runtime.Tests.OperationLifecycleExecution.sourceDeclaration,
    RoleCodeImage.toCodeImage, mapExecutableTargets?, OperationAction.mapTargets?,
    EffectRuntime.operationAction, EffectRuntime.relocateOperation,
    EffectRuntime.commandDeclaration, EffectRuntime.commandCall, EffectRuntime.relocateCommand,
    Std.HashMap.size_insert, Std.HashMap.size_empty, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty, Std.HashMap.mem_insert, Std.HashMap.not_mem_empty,
    List.foldlM_cons, List.foldlM_nil, List.mapM, List.mapM.loop,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Option.bind,
    Array.isEmpty, Array.size, Nat.reduceAdd, List.nil_append, List.cons_append,
    List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, decide_true, decide_false,
    Choreography.Projection.Project.trans, Choreography.Projection.Trans.trans,
    Choreography.Projection.Trans.transBranches, localTypeRToLocalType,
    localTypeRToLocalTypeAux, localTypeRBranchesToChoices, ↓reduceIte, ↓reduceDIte]

theorem malformed_joint_stage_image_eq :
    malformedJointRoleImage.toCodeImage ["B", "A"] = .ok malformedJointStageImage := by
  simp +decide only [malformedJointRoleImage, malformedJointCall, malformedJointParent,
    malformedJointStageImage, malformedJointStageCall, malformedJointStageDeclaration,
    jointRoleImage, jointStageImage, jointStageCall, jointStageDeclaration,
    parentDeclaration, readinessCall, readinessDeclaration, roleImage, declaration, call, global,
    Runtime.Tests.OperationLifecycleExecution.sourceDeclaration,
    RoleCodeImage.toCodeImage, mapExecutableTargets?, OperationAction.mapTargets?,
    EffectRuntime.operationAction, EffectRuntime.relocateOperation,
    EffectRuntime.commandDeclaration, EffectRuntime.commandCall, EffectRuntime.relocateCommand,
    Std.HashMap.size_insert, Std.HashMap.size_empty, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty, Std.HashMap.mem_insert, Std.HashMap.not_mem_empty,
    List.foldlM_cons, List.foldlM_nil, List.mapM, List.mapM.loop,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Option.bind,
    Array.isEmpty, Array.size, Nat.reduceAdd, List.nil_append, List.cons_append,
    List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, decide_true, decide_false,
    Choreography.Projection.Project.trans, Choreography.Projection.Trans.trans,
    Choreography.Projection.Trans.transBranches, localTypeRToLocalType,
    localTypeRToLocalTypeAux, localTypeRBranchesToChoices, ↓reduceIte, ↓reduceDIte]

theorem joint_stage_load_eq :
    loadChoreographyResult Runtime.Tests.NominalCommandExecution.empty jointStageImage =
      .ok jointStageInstalled 0 := by
  simp +decide only [loadChoreographyResult, validateImage_eq,
    jointStageImage, jointStageCall, jointStageDeclaration, parentDeclaration,
    readinessCall, readinessDeclaration, Runtime.Tests.OperationLifecycleExecution.sourceDeclaration,
    declaration, call, global, Runtime.Tests.NominalCommandExecution.empty,
    Runtime.Tests.NominalCommandExecution.config,
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

/-- The valid same-fixture load equation above is the positive control. Only the
joint child's selected budget is changed back to the old standalone2; the actual
assembler still succeeds and the public checked loader refuses BEFORE admission. -/
theorem malformed_joint_budget_is_refused_before_owner_admission :
    ((malformedJointRoleImage.toCodeImage ["B", "A"]).toOption.map
      (loadChoreographyResult Runtime.Tests.NominalCommandExecution.empty)) =
      some (.validationFailed "invalid nominal declarations or result continuations") := by
  simp only [malformed_joint_stage_image_eq, Except.toOption, Option.map]
  simp +decide only [loadChoreographyResult, validateImage_eq,
    malformedJointStageImage, malformedJointStageCall, malformedJointStageDeclaration,
    jointStageImage, jointStageCall, jointStageDeclaration, parentDeclaration,
    readinessCall, readinessDeclaration, Runtime.Tests.OperationLifecycleExecution.sourceDeclaration,
    declaration, call, global, Bind.bind, Pure.pure, Except.bind, Except.pure,
    decide_true, decide_false, ↓reduceIte, ↓reduceDIte]

theorem malformed_joint_retains_exact_other_policy_fields :
    malformedJointCall = { readinessCall with budgetTicks := call.budgetTicks } ∧
      malformedJointCall = { call with
        declaration := readinessDeclaration,
        enclosingOperation := "Save", onOk := 3, onErr := 7 } ∧
      parentDeclaration.budgetTicks = 5 ∧ readinessCall.budgetTicks = 5 ∧
      malformedJointCall.budgetTicks = 2 := by
  decide

theorem joint_stage_admission_eq :
    admitLoadedSessionOwner jointStageInstalled 0 "original-owner" =
      .ok (jointStageOwned, jointStageOwner) := by
  simp only [admitLoadedSessionOwner, jointStageInstalled, jointStageSession,
    jointStageCoroutine, jointStageOwned, jointStageOwner, List.lookup, List.filter,
    List.any, List.isEmpty, List.map_cons, List.map_nil, Array.toList,
    List.map_toArray, beq_self_eq_true, SessionTypes.ModelOwnershipState.claim,
    Bind.bind, Pure.pure, Except.bind, Except.pure,
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  all_goals rfl

theorem joint_stage_coro_eq :
    jointStageInstalled.coroutines[1]? = some (jointStageCoroutine "A" 1 2) := rfl

theorem joint_stage_endpoint_eq :
    (jointStageCoroutine "A" 1 2).ownedEndpoints.head? = some ({ sid := 0, role := "A" } : Endpoint) := rfl

theorem joint_blocked_eq : jointBlocked = (do
    let declared ← invokeInstalled jointStageOwned 1
    let begun ← invokeInstalled declared 1
    invokeInstalled begun 1) := by
  simp only [jointBlocked, joint_stage_image_eq, joint_stage_load_eq,
    joint_stage_coro_eq, joint_stage_endpoint_eq, joint_stage_admission_eq,
    Bind.bind, Pure.pure, Except.toOption, Option.bind]

theorem original_parent_owns_exact_blocked_readiness_child :
    (jointBlocked.map fun st =>
      st.coroutines[1]?.any (fun coro =>
        coro.effectCtx.calls == 1 && coro.nominalContinuation.isSome &&
        coro.operationContinuation.any (fun original => original.children.length == 1)) &&
      st.outstandingEffects.any (fun effect => effect.status == .blocked &&
        effect.orderingKey == 0 && effect.completedAtTick.isNone) &&
      st.operationInstances.length == 2).getD false = true := by
  simp only [jointSettled, jointResumed, joint_blocked_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      Runtime.Tests.OperationReadinessExecution.jointStageOwned,
      Runtime.Tests.OperationReadinessExecution.jointStageInstalled,
      Runtime.Tests.OperationReadinessExecution.jointStageSession,
      Runtime.Tests.OperationReadinessExecution.jointStageCoroutine,
      Runtime.Tests.OperationReadinessExecution.jointStageImage,
      Runtime.Tests.OperationReadinessExecution.jointStageCall,
      Runtime.Tests.OperationReadinessExecution.jointStageDeclaration,
      Runtime.Tests.OperationReadinessExecution.jointStageOwner,
      invokeInstalled, offerInstalled,
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

theorem original_parent_resolves_after_actual_readiness_consumption :
    (jointSettled.map fun st =>
      st.coroutines[1]?.any (fun coro =>
        coro.effectCtx.calls == 2 && coro.nominalContinuation.isNone &&
        coro.operationContinuation.any (fun original => original.resolved && original.children.length == 1)) &&
      st.outstandingEffects.any (fun effect => effect.status == .succeeded &&
        effect.orderingKey == 0 && effect.completedAtTick == some 1) &&
      st.sessions.any (fun entry => entry.2.ownership.consumedWitnesses == [1]) &&
      st.operationInstances.all (fun operation => operation.phase == .succeeded)).getD false = true := by
  simp only [jointSettled, jointResumed, joint_blocked_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      Runtime.Tests.OperationReadinessExecution.jointStageOwned,
      Runtime.Tests.OperationReadinessExecution.jointStageInstalled,
      Runtime.Tests.OperationReadinessExecution.jointStageSession,
      Runtime.Tests.OperationReadinessExecution.jointStageCoroutine,
      Runtime.Tests.OperationReadinessExecution.jointStageImage,
      Runtime.Tests.OperationReadinessExecution.jointStageCall,
      Runtime.Tests.OperationReadinessExecution.jointStageDeclaration,
      Runtime.Tests.OperationReadinessExecution.jointStageOwner,
      invokeInstalled, offerInstalled,
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

theorem output_refusal_cannot_spend_witness_or_resolve_original_parent :
    ((jointResumed false).map fun st =>
      st.coroutines[1]?.any (fun coro =>
        coro.effectCtx.calls == 2 && coro.nominalContinuation.any (fun original => original.returned.isSome) &&
        coro.operationContinuation.any (fun original => !original.resolved) &&
        (match coro.status with | .faulted _ => true | _ => false)) &&
      st.sessions.all (fun entry => entry.2.ownership.consumedWitnesses.isEmpty) &&
      !st.operationInstances.any (fun operation => operation.phase == .succeeded)).getD false = true := by
  simp only [jointSettled, jointResumed, joint_blocked_eq, Bind.bind, Pure.pure, Except.toOption, Option.bind,
    Bool.not_false, Bool.not_true, ↓reduceIte]
  all_goals
    simp only [Runtime.Tests.OperationLifecycleExecution.sourceStageOwned,
      Runtime.Tests.OperationLifecycleExecution.sourceStageInstalled,
      Runtime.Tests.OperationLifecycleExecution.sourceStageSession,
      Runtime.Tests.OperationLifecycleExecution.sourceStageCoroutine,
      Runtime.Tests.OperationLifecycleExecution.sourceStageImage,
      Runtime.Tests.OperationLifecycleExecution.sourceStageOwner,
      Runtime.Tests.OperationReadinessExecution.jointStageOwned,
      Runtime.Tests.OperationReadinessExecution.jointStageInstalled,
      Runtime.Tests.OperationReadinessExecution.jointStageSession,
      Runtime.Tests.OperationReadinessExecution.jointStageCoroutine,
      Runtime.Tests.OperationReadinessExecution.jointStageImage,
      Runtime.Tests.OperationReadinessExecution.jointStageCall,
      Runtime.Tests.OperationReadinessExecution.jointStageDeclaration,
      Runtime.Tests.OperationReadinessExecution.jointStageOwner,
      invokeInstalled, offerInstalled,
      Bind.bind, Pure.pure, Except.toOption, Option.bind, Option.map, Option.getD, Option.any,
      List.map_cons, List.map_nil, Array.map_eq_foldl, ↓reduceIte, ↓reduceDIte]
  all_goals decide

end Runtime.Tests.OperationReadinessExecution
