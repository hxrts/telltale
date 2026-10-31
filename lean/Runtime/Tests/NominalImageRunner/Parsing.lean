import Lean.Data.Json
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Runtime.Loader
import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.ProtocolMachine.Runtime.Json
import Choreography.Projection.Json

/-! # Runtime.Tests.NominalImageRunner.ParsingnnJSON parsing of nominal image runner inputs (operation declarations, resolutions, actions, scripts). Re-exported by `Runtime.Tests.NominalImageRunner`. -/

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
    costModel := {
      stepCost := fun _ => 1, minCost := 1, defaultBudget := 18446744073709551615,
      hMinCost := by intro _ _; exact Nat.le_refl 1,
      hMinPos := by exact Nat.le_refl 1
    },
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
  pure {
    declaration := declaration, enclosingOperation := operation,
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
  if value.getStr?.toOption == some "Cancelled" then return .cancelled
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
  | "resolve" => do
      let operation ← value.getObjValAs? String "operation"
      let outcome ← parseOperationResolution (← value.getObjVal? "outcome")
      return .resolve operation outcome
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
    | [role, localType] => pure ((← role.getStr?), (← localTypeRFromJson localType))
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

end Runtime.Tests.NominalImageRunner
