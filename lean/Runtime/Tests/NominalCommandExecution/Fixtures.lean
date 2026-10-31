import Std.Data.HashMap.Lemmas
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Runtime.Loader
import Runtime.ProtocolMachine.Semantics.Exec

/-! Nominal command execution test fixtures: the test effect runtime, nominal
command image and configuration, loader/invocation helpers, readiness preparation,
and fixture-only examples/theorems that do not need the private staging lemmas.
Re-exported by `Runtime.Tests.NominalCommandExecution`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Runtime.Tests.NominalCommandExecution
open Runtime.ProtocolMachine.Model

inductive TestEffect : Type
inductive Action where
  | plain
  | declaration (value : NominalCommandDeclaration)
  | command (value : NominalCommandCall)
  | operation (value : OperationAction)
  deriving DecidableEq
structure Context where
  calls : Nat := 0
  genericCalls : Nat := 0
  blockFirst : Bool := true
  fail : Bool := false
  wrongReply : Bool := false
  applicationError : Bool := false
  changeIdentity : Bool := false
  identity : String := "original"
  readiness : Option SessionTypes.ReadinessWitness := none
  deriving Inhabited

instance instEffectRuntimeTestEffect : EffectRuntime TestEffect where
  EffectAction := Action
  EffectCtx := Context
  exec := fun _ ctx => { ctx with genericCalls := ctx.genericCalls + 1 }
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
    let next := { ctx with
      calls := ctx.calls + 1,
      identity := if ctx.changeIdentity then "changed" else ctx.identity }
    if ctx.fail then (⟨.failure "original" "native observation remains semantic", none⟩, next)
    else if ctx.blockFirst && ctx.calls == 0 then (⟨.blocked, none⟩, next)
    else (⟨.success, some (.nominalCommand
      ⟨request.invocation + (if ctx.wrongReply then 1 else 0),
        if ctx.applicationError then .error "application denied" else .ok (match ctx.readiness with | some witness => .readiness witness | none => .bool true)⟩)⟩, next)
instance : Inhabited (EffectRuntime.EffectCtx TestEffect) := ⟨{}⟩
instance : EffectGuardBridge TestEffect UnitGuard where bridge := fun _ => ()
instance : PersistenceEffectBridge UnitPersist TestEffect where bridge := fun _ => ()

def declaration : NominalCommandDeclaration := ⟨"Store", "save", true, none⟩
def call : NominalCommandCall :=
  { declaration := declaration, enclosingOperation := "Save", role := "A",
    agreementProfile := ⟨"SelectedLocal", .immediate, .noAgreement, .none, .none, .witness⟩,
    progressContract := "original-progress", progressWindow := "original-window",
    budgetTicks := 2, result := 1, onOk := 2, onErr := 4 }
def global : GlobalType := .comm "A" "B"
  [({ name := "Ready" }, .end), ({ name := "Denied" }, .end)]
def roleImage : RoleCodeImage UnitGuard TestEffect :=
  { programs := ({} : Std.HashMap Role (Bytecode UnitGuard TestEffect))
      |>.insert "A" #[.invoke (.declaration declaration), .invoke (.command call),
        .offer 0 "Ready", .halt, .offer 0 "Denied", .halt]
      |>.insert "B" #[.choose 0 [("Ready", 1), ("Denied", 1)], .halt],
    localTypes := ({} : Std.HashMap Role SessionTypes.LocalTypeR.LocalTypeR)
      |>.insert "A" (Choreography.Projection.Project.trans global "A")
      |>.insert "B" (Choreography.Projection.Project.trans global "B"),
    globalType := global }
/-- A deliberately nonzero command-role entry exercises actual role slicing. -/
def image : Except String (CodeImage UnitGuard TestEffect) :=
  roleImage.toCodeImage ["B", "A"]

def config : ProtocolMachineConfig UnitIdentity UnitGuard UnitPersist TestEffect UnitVerify :=
  { bufferConfig := fun _ => unitBufferConfig, schedPolicy := .cooperative,
    violationPolicy := { allow := fun _ => false }, flowPolicy := unitFlowPolicy,
    spatialOk := fun _ => true, transportOk := fun _ _ => true,
    complianceProof := fun _ => ((), ()), maxCoroutines := 1024, maxSessions := 256,
    monitorMode := .sessionTypePrecheck, guardChain := unitGuardChain,
    proofConfig := { guardChainWf := unitGuardChainWf }, roleSigningKey := fun _ => (),
    costModel := {
      stepCost := fun _ => 1, minCost := 1, defaultBudget := 100,
      hMinCost := by intro _ _; exact Nat.le_refl 1,
      hMinPos := by exact Nat.le_refl 1
    },
    speculationEnabled := false }
abbrev State := ProtocolMachineState UnitIdentity UnitGuard UnitPersist TestEffect UnitVerify

def empty : State :=
  { config := config,
    code := { code := #[], entryPoints := [], localTypes := [], handlerTypes := [], metadata := ProgramMeta.empty },
    programs := #[], coroutines := #[], buffers := [], persistent := (), nextCoroId := 0,
    nextSessionId := 0, arena := { slots := #[], nextFree := 0, capacity := 0, inv := Nat.le_refl 0 },
    sessions := [], resourceStates := {}, guardResources := [],
    sched := { policy := .cooperative, readyQueue := [], blockedSet := {}, timeslice := 1, stepCount := 0 },
    monitor := { step := fun sk => some sk }, obsTrace := [], clock := 0,
    crashedSites := [], partitionedEdges := [], mask := (), ghostSessions := default, progressSupply := () }

def ordinaryLoaded : Option State := do
  let executable ← image.toOption
  match loadChoreographyResult empty executable with
  | .ok st _ => some st
  | _ => none

def loaded : Option State := do
  let st ← ordinaryLoaded
  let coro ← st.coroutines[1]?
  let endpoint ← coro.ownedEndpoints.head?
  let (admitted, _) ← (admitLoadedSessionOwner st endpoint.sid "original").toOption
  return admitted

/-- Fetch and execute the actual installed opcode; tests cannot pass a different
call descriptor directly to the command producer. -/
def invokeInstalled (st : State) (index : Nat) : Option State := do
  let coro ← st.coroutines[index]?
  let program ← st.programs[coro.programId]?
  match program.code[coro.pc]? with
  | some (.invoke action) =>
      pure (commitPack st coro.id (stepInvoke st coro action)).1
  | _ => none

/-! Proof staging. These normal forms are never used as loader or owner inputs
without the exact producer equations below. In particular, `stageOwned` is model
data whose equality is proved against `admitLoadedSessionOwner`, not host custody. -/
def blocked : Option State := do
  let st ← loaded
  let declared ← invokeInstalled st 1
  invokeInstalled declared 1

def resumed : Option State := do
  let st ← blocked
  invokeInstalled { st with clock := 2 } 1

def preservesExecutable : Bool := match image with
  | .error _ => false
  | .ok executable => match executable.toRoleCodeImage with
    | .error _ => false
    | .ok restored => match restored.programs["A"]? with
      | some code => match (code[1]? : Option (Instr UnitGuard TestEffect)) with
        | some (Instr.invoke (Action.command actual)) => decide (actual = call) && code.size == 6
        | _ => false
      | _ => false

def view (st : State) : Option
    (CoroutineState UnitGuard TestEffect × OutstandingEffect × OperationInstance) := do
  let coro ← st.coroutines[1]?
  let effect ← st.outstandingEffects.head?
  let operation ← st.operationInstances.head?
  pure (coro, effect, operation)

example : preservesExecutable = true := by
  simp +decide only [instEffectRuntimeTestEffect, EffectRuntime.operationAction, EffectRuntime.commandDeclaration, EffectRuntime.commandCall, EffectRuntime.relocateCommand,
    declaration, call, global, roleImage, image, preservesExecutable, RoleCodeImage.toCodeImage,
    mapExecutableTargets?, CodeImage.toRoleCodeImage, Std.HashMap.size_insert,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty, Std.HashMap.size_empty,
    Std.HashMap.mem_insert, Std.HashMap.not_mem_empty, List.foldlM_cons, List.foldlM_nil,
    List.mapM, Except.bind, Option.bind, List.foldl, List.take, List.drop, Array.size,
    Nat.min_def, Nat.reduceAdd, Nat.reduceSub, List.nil_append, List.cons_append,
    List.reverse_cons, List.reverse_nil, List.length_cons, List.length_nil, List.mapM.loop,
    Bind.bind, Pure.pure, Except.pure, ↓reduceIte]
example : (match image with | .ok value => nominalProgramValid value.program | _ => false) = true := by
  simp +decide only [
    declaration, call, global, roleImage, image, RoleCodeImage.toCodeImage, mapExecutableTargets?,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty,
    Std.HashMap.size_empty, Std.HashMap.mem_insert, Std.HashMap.not_mem_empty, List.foldlM_cons,
    List.foldlM_nil, List.mapM, Except.bind, Option.bind, Array.size, Nat.reduceAdd,
    List.nil_append, List.cons_append, List.length_cons, List.length_nil, List.mapM.loop,
    Bind.bind, Pure.pure, Except.pure, ↓reduceIte]
/-- Set only the actual installed coroutine's selected test provider context. -/
def prepared (context : Context) : Option State := do
  let st ← loaded
  let st ← invokeInstalled st 1
  let coro ← st.coroutines[1]?
  pure { st with coroutines := st.coroutines.set! 1 { coro with effectCtx := context } }

inductive MissingRelocation : Type
instance : EffectRuntime MissingRelocation where
  EffectAction := Action
  EffectCtx := Unit
  exec := fun _ _ => ()
  commandCall := fun action => match action with
    | .command value => some value | _ => none

inductive LyingRelocation : Type
instance : EffectRuntime LyingRelocation where
  EffectAction := Action
  EffectCtx := Unit
  exec := fun _ _ => ()
  commandCall := fun action => match action with
    | .command value => some value | _ => none
  relocateCommand := fun original _ => some original

example : (mapExecutableTargets? (γ := UnitGuard) (ε := MissingRelocation)
    (fun pc => some (pc + 7)) (.invoke (Action.command call))).isNone = true := by decide
example : (mapExecutableTargets? (γ := UnitGuard) (ε := LyingRelocation)
    (fun pc => some (pc + 7)) (.invoke (Action.command call))).isNone = true := by decide

/-- A real cross-role continuation cannot become an in-role target by slicing
or silently recompiling the local communication type. -/
example : (match image with
  | .error _ => false
  | .ok executable =>
      let forged := { executable with
        program := { executable.program with
        code := executable.program.code.set! 3 (.invoke (.command { call with onOk := 0, onErr := 6 })) } }
      (forged.toRoleCodeImage).toOption.isNone) = true := by
  simp +decide only [
    declaration, call, global, roleImage, image, RoleCodeImage.toCodeImage, mapExecutableTargets?,
    Std.HashMap.size_insert, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty,
    Std.HashMap.size_empty, Std.HashMap.mem_insert, Std.HashMap.not_mem_empty, List.foldlM_cons,
    List.foldlM_nil, List.mapM, Except.bind, Option.bind, Array.size, Nat.reduceAdd,
    List.nil_append, List.cons_append, List.length_cons, List.length_nil, List.mapM.loop,
    Bind.bind, Pure.pure, Except.pure, ↓reduceIte]

/-- Model ownership is admitted independently before callback evidence exists. -/
def readinessPrepared (mutation : Nat := 0) : Option State := do
  let readinessDeclaration := { declaration with readinessPredicate := some "Store.save" }
  let readinessCall := { call with declaration := readinessDeclaration }
  let roles := { roleImage with
    programs := roleImage.programs.insert "A"
      #[.invoke (.declaration readinessDeclaration), .invoke (.command readinessCall),
        .offer 0 "Ready", .halt, .offer 0 "Denied", .halt] }
  let executable ← (roles.toCodeImage ["B", "A"]).toOption
  let st ← match loadChoreographyResult empty executable with | .ok st _ => some st | _ => none
  let coro ← st.coroutines[1]?
  let endpoint ← coro.ownedEndpoints.find? (fun endpoint => endpoint.role == "A")
  let (st, owner) ← (admitLoadedSessionOwner st endpoint.sid "original-owner").toOption
  let coro ← st.coroutines[1]?
  let session ← st.sessions.lookup endpoint.sid
  let (issued, original) ← (session.ownership.issueReadiness owner "Store.save").toOption
  let witness := match mutation with
    | 1 => { original with witnessId := original.witnessId + 1 }
    | 2 => { original with predicateRef := "Other.ready" }
    | _ => original
  let ownership ← if mutation == 3 then (issued.consumeReadiness owner original).toOption else some issued
  let st := { st with
    sessions := st.sessions.map (fun (sid, current) =>
      if sid == endpoint.sid then (sid, { current with ownership := ownership }) else (sid, current)),
    coroutines := st.coroutines.set! 1 { coro with effectCtx := { blockFirst := false, readiness := some witness } } }
  invokeInstalled st 1

def registeredReadiness : Option (SessionTypes.ModelOwnershipState × SessionTypes.ModelOwner × SessionTypes.ReadinessWitness) := do
  let (claimed, owner) ← (({} : SessionTypes.ModelOwnershipState).claim 7 "original").toOption
  let (issued, witness) ← (claimed.issueReadiness owner "Store.save").toOption
  pure (issued, owner, witness)

theorem readiness_model_exact_owner_generation_session_scope :
    (match registeredReadiness with
    | some (state, owner, witness) =>
      [ { witness with sessionId := 8 }, { witness with ownerId := "foreign" },
        { witness with generation := 1 }, { witness with scope := .fragments [] } ].all
          (fun changed => (state.consumeReadiness owner changed).toOption.isNone)
    | none => false) = true := by decide

theorem readiness_model_pending_and_changed_owner_refuse_before_consumption :
    (match registeredReadiness with
    | some (state, owner, witness) =>
      let pending := { state with transferPending := true }
      let changed := { state with current := some { owner with generation := owner.generation + 1 } }
      (pending.consumeReadiness owner witness).toOption.isNone &&
      (changed.consumeReadiness owner witness).toOption.isNone &&
      state.issuedReadiness.length == 1 && state.consumedWitnesses.isEmpty
    | none => false) = true := by decide


end Runtime.Tests.NominalCommandExecution
