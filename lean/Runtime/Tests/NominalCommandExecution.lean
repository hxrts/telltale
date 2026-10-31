import Std.Data.HashMap.Lemmas
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Runtime.Loader
import Runtime.ProtocolMachine.Semantics.Exec
import Runtime.Tests.NominalCommandExecution.Fixtures


/-! Executable nominal protocol tests. These instantiate the canonical loader,
coroutine, outstanding-effect, operation and commit producers. They do not model
Rust host-handle issuance or physical provider cleanup. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Runtime.Tests.NominalCommandExecution
open Runtime.ProtocolMachine.Model


private def stageImage (predicate : Option String) : CodeImage UnitGuard TestEffect :=
  let declared := { declaration with readinessPredicate := predicate }
  let selected := { call with declaration := declared, onOk := 4, onErr := 6 }
  let branches := [({ name := "Ready" }, none, SessionTypes.LocalTypeR.LocalTypeR.end),
    ({ name := "Denied" }, none, SessionTypes.LocalTypeR.LocalTypeR.end)]
  { program := {
      code := #[.choose 0 [("Ready", 1), ("Denied", 1)], .halt,
        .invoke (.declaration declared), .invoke (.command selected),
        .offer 0 "Ready", .halt, .offer 0 "Denied", .halt],
      entryPoints := [("B", 0), ("A", 2)],
      localTypes := [("B", .branch "A" [("Ready", .end_), ("Denied", .end_)]),
        ("A", .select "B" [("Ready", .end_), ("Denied", .end_)])],
      localTypesR := [("B", .recv "A" branches), ("A", .send "B" branches)],
      handlerTypes := [], metadata := ProgramMeta.empty }, globalType := global }

private def stageCoroutine (role : String) (id pc : Nat) : CoroutineState UnitGuard TestEffect :=
  let endpoint : Endpoint := { sid := 0, role }
  { id, programId := 0, role, pc,
    regs := (Array.replicate config.numRegisters .unit).set! 0 (.chan endpoint),
    status := .ready, effectCtx := default, ownedEndpoints := [endpoint],
    progressTokens := [], knowledgeSet := [], costBudget := 100, specState := none }

private def stageSession (predicate : Option String) : SessionState UnitVerify :=
  let edge : Edge := { sid := 0, sender := "A", receiver := "B" }
  { scope := { id := 0 }, sid := 0, roles := ["B", "A"],
    endpoints := [{ sid := 0, role := "B" }, { sid := 0, role := "A" }],
    localTypes := (stageImage predicate).program.localTypes.map
      (fun entry => ({ sid := 0, role := entry.1 }, entry.2)),
    traces := initDEnv 0 ["B", "A"], buffers := [(edge, [])],
    handlers := [(edge, 0)], epoch := 0, phase := .active }

private def stageInstalled (predicate : Option String) : State :=
  let edge : Edge := { sid := 0, sender := "A", receiver := "B" }
  { empty with
    programs := #[(stageImage predicate).program],
    coroutines := #[stageCoroutine "B" 0 0, stageCoroutine "A" 1 2],
    buffers := [(edge, [])], sessions := [(0, stageSession predicate)],
    sched := { empty.sched with readyQueue := [0, 1] },
    obsTrace := [{ tick := 0, event := .opened 0 ["B", "A"] }],
    nextCoroId := 2, nextSessionId := 1 }

private def stageOwner (name : String) : SessionTypes.ModelOwner :=
  ⟨0, name, 0, .session⟩

private def stageOwned (predicate : Option String) (name : String) : State :=
  let owner := stageOwner name
  let installed := stageInstalled predicate
  { installed with
    sessions := [(0, { stageSession predicate with
      ownership := { current := some owner } })],
    coroutines := installed.coroutines.map
      (fun coroutine => { coroutine with issuedModelOwner := some owner }) }

private theorem stage_image_eq : image = .ok (stageImage none) := by
  simp +decide only [instEffectRuntimeTestEffect, EffectRuntime.operationAction, EffectRuntime.commandDeclaration, EffectRuntime.commandCall, EffectRuntime.relocateCommand,
    image, roleImage, stageImage, declaration, call, global,
    RoleCodeImage.toCodeImage, mapExecutableTargets?,
    Std.HashMap.size_insert, Std.HashMap.size_empty,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty,
    Std.HashMap.mem_insert, Std.HashMap.not_mem_empty,
    List.foldlM_cons, List.foldlM_nil, List.mapM, List.mapM.loop,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Option.bind,
    Array.isEmpty, Array.size, Nat.reduceAdd,
    List.nil_append, List.cons_append, List.length_cons, List.length_nil,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    decide_true, decide_false,
    Choreography.Projection.Project.trans, Choreography.Projection.Trans.trans,
    Choreography.Projection.Trans.transBranches,
    localTypeRToLocalType, localTypeRToLocalTypeAux, localTypeRBranchesToChoices,
    ↓reduceIte, ↓reduceDIte]

private theorem stage_load_eq (readiness : Bool) :
    loadChoreographyResult empty (stageImage (if readiness then some "Store.save" else none)) =
      .ok (stageInstalled (if readiness then some "Store.save" else none)) 0 := by
  cases readiness <;> simp +decide only [
    loadChoreographyResult, validateImage_eq,
    stageImage, declaration, call, global, empty, config,
    Choreography.Projection.Project.projectR?,
    Choreography.Projection.Project.trans, Choreography.Projection.Trans.trans,
    Choreography.Projection.Trans.transBranches,
    Choreography.Projection.Projectb.projectb,
    Choreography.Projection.Projectb.projectbBranches,
    List.find?_cons, List.find?_nil, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Except.toOption,
    Option.map, Option.bind, decide_true, decide_false,
    nextFreshSessionId, sessionIdAvailable, existingSessionIds,
    ↓reduceIte, ↓reduceDIte]
  all_goals
    -- This can apply only after ACTUAL validation/capacity/fresh-ID branches
    -- have reduced to the actual ok(core state, 0) constructor. Any unresolved
    -- validation match must remain a failed producer proof here.
    apply congrArg (fun state : State => ChoreographyLoadResult.ok state 0)
    -- Compare the real private loadChoreographyCore output to stageInstalled.
    -- Its edge collectors are structural; no new equality axiom/API is needed.
    rfl

private theorem stage_plain_load_eq :
    loadChoreographyResult empty (stageImage none) = .ok (stageInstalled none) 0 :=
  stage_load_eq false

private theorem stage_ready_load_eq :
    loadChoreographyResult empty (stageImage (some "Store.save")) =
      .ok (stageInstalled (some "Store.save")) 0 :=
  stage_load_eq true

private theorem stage_admission_eq (predicate : Option String) (name : String)
    (named : name.isEmpty = false) :
    admitLoadedSessionOwner (stageInstalled predicate) 0 name =
      .ok (stageOwned predicate name, stageOwner name) := by
  -- Reduce the ACTUAL installed-session lookup, nonempty/unclaimed-coro
  -- guard, conditional endpoint map and registry claim; do not omit them in
  -- an asserted normal form of an arbitrary state.
  simp +decide only [admitLoadedSessionOwner, stageInstalled, stageSession,
    stageCoroutine, stageOwned, stageOwner, List.lookup, List.filter,
    List.any, List.isEmpty, List.map_cons, List.map_nil,
    Array.toList, List.map_toArray, beq_self_eq_true, SessionTypes.ModelOwnershipState.claim,
    named, Bind.bind, Pure.pure, Except.bind, Except.pure,
    Bool.false_or, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, ↓reduceDIte]
  all_goals rfl

private theorem stage_ordinary_eq : ordinaryLoaded = some (stageInstalled none) := by
  simp only [ordinaryLoaded, stage_image_eq, Bind.bind, Pure.pure,
    Except.toOption, Option.bind, stage_plain_load_eq]

private theorem stage_loaded_eq : loaded = some (stageOwned none "original") := by
  unfold loaded
  rw [stage_ordinary_eq]
  change (match admitLoadedSessionOwner (stageInstalled none) 0 "original" with
    | .ok admitted => some admitted.1 | .error _ => none) = _
  rw [stage_admission_eq none "original" (by decide)] <;> rfl

theorem ordinary_nominal_loader_cannot_reconstruct_original_owner :
    ((ordinaryLoaded.bind (fun st => invokeInstalled st 1)).bind
      (fun st => invokeInstalled st 1) |>.map fun st =>
        st.outstandingEffects.isEmpty && st.operationInstances.isEmpty && st.nextEffectId == 0 &&
        st.coroutines[1]?.any (fun coro => coro.effectCtx.calls == 0 &&
          match coro.status with | .faulted _ => true | _ => false)).getD false = true := by
  simp only [stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

example : (match blocked with
  | some st => match view st with
    | some (coro, effect, _) => st.nextEffectId == 1 && st.outstandingEffects.length == 1 &&
        coro.effectCtx.calls == 1 && coro.effectCtx.genericCalls == 0 &&
        decide (effect.status = .blocked) && effect.orderingKey == 0
    | _ => false
  | _ => false) = true := by
  simp only [blocked, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide
example : (match resumed with
  | some st => match view st with
    | some (coro, effect, operation) => st.nextEffectId == 1 && coro.effectCtx.calls == 2 &&
        coro.pc == 4 && decide (coro.regs[1]? = some (.bool true)) &&
        decide (effect.status = .succeeded) && operation.requiresProof &&
        st.effectExchanges.length == 2
    | _ => false
  | _ => false) = true := by
  simp only [blocked, resumed, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

/-- Still-Blocked expiry refuses before another callback, without resetting the
original occurrence or replacing its original progress/window. -/
example : (match blocked.bind (fun st => invokeInstalled { st with clock := 3 } 1) with
  | some st => match view st with
    | some (coro, effect, _) => coro.effectCtx.calls == 1 && st.nextEffectId == 1 &&
        effect.orderingKey == 0 && decide (effect.status = .blocked) &&
        coro.nominalContinuation.isSome
    | _ => false
  | _ => false) = true := by
  simp only [blocked, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

/-- A static declaration cannot be borrowed from another role's prefix. -/
example : (match image with
  | .ok executable => nominalProgramValid { executable.program with
      code := executable.program.code.set! 2 .yield }
  | _ => true) = false := by
  simp +decide only [
    declaration, call, global, roleImage, image, RoleCodeImage.toCodeImage, mapExecutableTargets?,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty,
    Std.HashMap.size_empty, Std.HashMap.mem_insert, Std.HashMap.not_mem_empty, List.foldlM_cons,
    List.foldlM_nil, List.mapM, Except.bind, Option.bind, Array.size, Nat.reduceAdd,
    List.nil_append, List.cons_append, List.length_cons, List.length_nil, List.mapM.loop,
    Bind.bind, Pure.pure, Except.pure, ↓reduceIte]

/-- Host semantic identity changes refuse the same original occurrence rather
than issuing a replacement or invoking the new handler contract. -/
example : (match blocked.bind (fun st => do
    let coro ← st.coroutines[1]?
    invokeInstalled { st with
      coroutines := st.coroutines.set! 1
        { coro with effectCtx := { coro.effectCtx with identity := "foreign" } } } 1) with
  | some st => match view st with
    | some (coro, _, _) => coro.effectCtx.calls == 1 && st.nextEffectId == 1 &&
        coro.nominalContinuation.isSome
    | _ => false
  | _ => false) = true := by
  simp only [blocked, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

example : (match (prepared { blockFirst := false, applicationError := true }).bind
    (fun st => invokeInstalled st 1) with
  | some st => match view st with
    | some (coro, effect, operation) => coro.pc == 6 &&
        decide (coro.regs[1]? = some (.string "application denied")) &&
        decide (effect.status = .succeeded) && operation.requiresProof &&
        decide (operation.agreementProfile = some call.agreementProfile)
    | _ => false
  | _ => false) = true := by
  simp only [prepared, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

/-- Host semantic Failure is distinct from a typed application Err branch and
from an independent post-callback identity refusal. The raw original outcome
and independent refusal remain separately inspectable. -/
example : (match (prepared { blockFirst := false, fail := true, changeIdentity := true }).bind
    (fun st => invokeInstalled st 1) with
  | some st => match view st, st.effectExchanges.head? with
    | some (coro, effect, _), some exchange =>
        decide (effect.status = .failed) && coro.pc == 3 &&
        decide (exchange.outcome.status = .failure "original" "native observation remains semantic") &&
        (coro.nominalContinuation.bind (fun original => original.validationFailure)).isSome &&
        decide (coro.regs[1]? = some .unit)
    | _, _ => false
  | _ => false) = true := by
  simp only [prepared, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

example : (match (prepared { blockFirst := false, wrongReply := true }).bind
    (fun st => invokeInstalled st 1) with
  | some st => match view st, st.effectExchanges.head? with
    | some (coro, effect, _), some exchange =>
        decide (effect.status = .failed) && coro.pc == 3 &&
        decide (exchange.outcome.status = .success) &&
        (coro.nominalContinuation.bind (fun original => original.returned)).isNone &&
        decide (coro.regs[1]? = some .unit)
    | _, _ => false
  | _ => false) = true := by
  simp only [prepared, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

/-- Actual output-gate refusal retains the issued occurrence and its genuine
returned value without changing the result register or publishing success. -/
example : (match (prepared { blockFirst := false }).bind (fun st =>
    invokeInstalled { st with
      config := { st.config with
      outputCondition := { verify := fun _ => false } } } 1) with
  | some st => match view st with
    | some (coro, effect, _) => coro.effectCtx.calls == 1 && coro.pc == 3 &&
        decide (effect.status = .pending) &&
        decide ((coro.nominalContinuation.bind (fun original => original.returned)) = some (.ok (.bool true))) &&
        decide (coro.regs[1]? = some .unit) && st.effectExchanges.length == 1
    | _ => false
  | _ => false) = true := by
  simp only [prepared, stage_loaded_eq, stage_ordinary_eq,
    stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

/-! A typed action adapter is required to preserve executable continuations;
parser/classifier support alone cannot authorize a relocation. -/
private theorem stage_readiness_image_eq :
    ({ roleImage with
      programs := roleImage.programs.insert "A"
        #[.invoke (.declaration { declaration with readinessPredicate := some "Store.save" }),
          .invoke (.command { call with declaration :=
            { declaration with readinessPredicate := some "Store.save" } }),
          .offer 0 "Ready", .halt, .offer 0 "Denied", .halt] }.toCodeImage ["B", "A"]) =
      .ok (stageImage (some "Store.save")) := by
  simp +decide only [instEffectRuntimeTestEffect, EffectRuntime.operationAction, EffectRuntime.commandDeclaration, EffectRuntime.commandCall, EffectRuntime.relocateCommand,
    roleImage, stageImage, declaration, call, global,
    RoleCodeImage.toCodeImage, mapExecutableTargets?,
    Std.HashMap.size_insert, Std.HashMap.size_empty,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty,
    Std.HashMap.mem_insert, Std.HashMap.not_mem_empty,
    List.foldlM_cons, List.foldlM_nil, List.mapM, List.mapM.loop,
    Bind.bind, Pure.pure, Except.bind, Except.pure, Option.bind,
    Array.isEmpty, Array.size, Nat.reduceAdd,
    List.nil_append, List.cons_append, List.length_cons, List.length_nil,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    decide_true, decide_false,
    Choreography.Projection.Project.trans, Choreography.Projection.Trans.trans,
    Choreography.Projection.Trans.transBranches,
    localTypeRToLocalType, localTypeRToLocalTypeAux, localTypeRBranchesToChoices,
    ↓reduceIte, ↓reduceDIte]

/-- The unchanged post-admission issuer/consumer transaction. No witness is
inferred from the normal-form owner or fabricated callback data. -/
private def stageReadinessPrepared (mutation : Nat) : Option State := do
  let st := stageOwned (some "Store.save") "original-owner"
  let owner := stageOwner "original-owner"
  let coro ← st.coroutines[1]?
  let endpoint ← coro.ownedEndpoints.find? (fun endpoint => endpoint.role == "A")
  let session ← st.sessions.lookup endpoint.sid
  let (issued, original) ← (session.ownership.issueReadiness owner "Store.save").toOption
  let witness := match mutation with
    | 1 => { original with witnessId := original.witnessId + 1 }
    | 2 => { original with predicateRef := "Other.ready" }
    | _ => original
  let ownership ← if mutation == 3 then (issued.consumeReadiness owner original).toOption else some issued
  let st := { st with
    sessions := st.sessions.map (fun (sid, current) =>
      if sid == endpoint.sid then (sid, { current with ownership }) else (sid, current)),
    coroutines := st.coroutines.set! 1 { coro with effectCtx := { blockFirst := false, readiness := some witness } } }
  invokeInstalled st 1

private theorem stage_readiness_eq (mutation : Nat) :
    readinessPrepared mutation = stageReadinessPrepared mutation := by
  simp only [readinessPrepared, stage_readiness_image_eq,
    Bind.bind, Pure.pure, Except.toOption, Option.bind, stage_ready_load_eq]
  have installed_coro :
      (stageInstalled (some "Store.save")).coroutines[1]? =
        some (stageCoroutine "A" 1 2) := rfl
  have installed_endpoint :
      (stageCoroutine "A" 1 2).ownedEndpoints.find?
          (fun endpoint => endpoint.role == "A") =
        some ({ sid := 0, role := "A" } : Endpoint) := by
    simp only [stageCoroutine, List.find?_cons, beq_self_eq_true, ↓reduceIte]
  simp only [installed_coro, installed_endpoint, Option.bind]
  -- Rewrite the actual exposed admission without restating its monadic tail.
  have owned_coro :
      (stageOwned (some "Store.save") "original-owner").coroutines[1]? =
        some ({ stageCoroutine "A" 1 2 with
          issuedModelOwner := some (stageOwner "original-owner") }) := by
    simp only [stageOwned, stageInstalled, List.map_toArray, List.map_cons, List.map_nil] <;> rfl
  rw [stage_admission_eq (some "Store.save") "original-owner" (by decide)] <;>
    simp only [stageReadinessPrepared, owned_coro, installed_endpoint,
      Bind.bind, Pure.pure, Option.bind] <;> rfl

/-- Real installed invocation consumes the exact session-issued witness once. -/
theorem readiness_actual_commit_single_use :
    (match (readinessPrepared 0).bind (fun st => invokeInstalled st 1) with
    | some st => match view st with
      | some (coro, effect, _) => match coro.regs[1]?, coro.ownedEndpoints.head? with
        | some (Value.readiness witness), some endpoint => match st.sessions.lookup endpoint.sid with
          | some session => session.ownership.consumedWitnesses.contains witness.witnessId &&
              session.ownership.issuedReadiness.isEmpty && coro.pc == 4 &&
              decide (effect.status = .succeeded) && coro.effectCtx.calls == 1
          | none => false
        | _, _ => false
      | _ => false
    | none => false) = true := by
  simp only [stage_readiness_eq, stageReadinessPrepared, stageOwned, stageInstalled,
    List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

/-- Forged payload, wrong predicate and replayed consumed evidence never branch. -/
theorem readiness_actual_forgery_predicate_and_reuse_refused :
    ([1, 2, 3].all (fun mutation =>
      match (readinessPrepared mutation).bind (fun st => invokeInstalled st 1) with
      | some st => match st.coroutines[1]? with
        | some coro => decide (coro.regs[1]? = some .unit) &&
            (match coro.status with | .faulted _ => true | _ => false)
        | none => false
      | none => false)) = true := by
  simp only [stage_readiness_eq, stageReadinessPrepared, stageOwned, stageInstalled,
    List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

/-- Existing output refusal leaves actual returned witness and registry live. -/
theorem readiness_actual_output_refusal_retains_original :
    (match (readinessPrepared 0).bind (fun st => invokeInstalled
      { st with config := { st.config with outputCondition := { verify := fun _ => false } } } 1) with
    | some st => match view st with
      | some (coro, effect, _) => match coro.ownedEndpoints.head? with
        | some endpoint => match st.sessions.lookup endpoint.sid with
          | some session => session.ownership.issuedReadiness.length == 1 &&
              session.ownership.consumedWitnesses.isEmpty && coro.pc == 3 &&
              coro.nominalContinuation.isSome && coro.effectCtx.calls == 1 &&
              decide (effect.status = .pending) && decide (coro.regs[1]? = some .unit)
          | none => false
        | none => false
      | none => false
    | none => false) = true := by
  simp only [stage_readiness_eq, stageReadinessPrepared, stageOwned, stageInstalled,
    List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

theorem readiness_actual_boolean_cannot_authorize :
    (match (readinessPrepared 0).bind (fun st => do
      let coro ← st.coroutines[1]?
      invokeInstalled { st with
        coroutines := st.coroutines.set! 1
          { coro with effectCtx := { coro.effectCtx with readiness := none } } } 1) with
    | some st => match st.coroutines[1]? with
      | some coro => decide (coro.regs[1]? = some .unit) && coro.effectCtx.calls == 1 &&
          (match coro.status with | .faulted _ => true | _ => false)
      | none => false
    | none => false) = true := by
  simp only [stage_readiness_eq, stageReadinessPrepared, stageOwned, stageInstalled,
    List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

theorem readiness_retained_result_rechecks_changed_generation_before_reuse :
    (match (readinessPrepared 0).bind (fun st => invokeInstalled
      { st with config := { st.config with outputCondition := { verify := fun _ => false } } } 1) |>.bind (fun st => do
        let coro ← st.coroutines[1]?
        let endpoint ← coro.ownedEndpoints.head?
        let session ← st.sessions.lookup endpoint.sid
        let owner ← session.ownership.current
        let changed := { session.ownership with current := some { owner with generation := owner.generation + 1 } }
        invokeInstalled { st with
          config := config, sessions := st.sessions.map (fun (sid, current) =>
          if sid == endpoint.sid then (sid, { current with ownership := changed }) else (sid, current)) } 1) with
    | some st => match st.coroutines[1]? with
      | some coro => coro.effectCtx.calls == 1 && decide (coro.regs[1]? = some .unit) &&
          coro.nominalContinuation.isSome &&
          (match coro.status with | .faulted _ => true | _ => false)
      | none => false
    | none => false) = true := by
  simp only [stage_readiness_eq, stageReadinessPrepared, stageOwned, stageInstalled,
    List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide


/-- A new registry generation cannot refresh a stale installed coroutine owner. -/
theorem readiness_before_issuance_never_reconstructs_current_owner :
    (match (readinessPrepared 0).bind (fun st => do
        let coro ← st.coroutines[1]?
        let endpoint ← coro.ownedEndpoints.head?
        let session ← st.sessions.lookup endpoint.sid
        let owner ← session.ownership.current
        let changed := { session.ownership with current := some { owner with generation := owner.generation + 1 } }
        invokeInstalled { st with
          sessions := st.sessions.map (fun (sid, current) =>
          if sid == endpoint.sid then (sid, { current with ownership := changed }) else (sid, current)) } 1) with
    | some st => match st.coroutines[1]? with
      | some coro => coro.effectCtx.calls == 0 && decide (coro.regs[1]? = some .unit) &&
          (match coro.status with | .faulted _ => true | _ => false)
      | none => false
    | none => false) = true := by
  simp only [stage_readiness_eq, stageReadinessPrepared, stageOwned, stageInstalled,
    List.map_toArray, List.map_cons, List.map_nil,
    Bind.bind, Pure.pure, Option.bind, Option.map, Option.getD] <;> decide

end Runtime.Tests.NominalCommandExecution
