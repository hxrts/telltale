import Runtime.ProtocolMachine.Model.Core
import Runtime.ProtocolMachine.Model.TypeClasses
import Runtime.ProtocolMachine.Model.CompileLocalTypeR
import SessionTypes.LocalTypeR

/-! # Program Images and Compilation

`Program`, `CodeImage`, and `UntrustedImage`, the program representation that the
protocol machine loads and executes. A `Program` is bytecode plus per-role entry points, local types,
handler types, and source metadata. A `CodeImage` bundles executable program payload with
its global type. An
`UntrustedImage` is an unverified program pending signature and typing checks, used by
the code loading pipeline.
-/

/-
The Problem. The protocol machine needs a program representation that bundles bytecode with type
information, entry points, and verification evidence. The loading pipeline must
distinguish trusted (verified) from untrusted (pending verification) code.

Solution Structure. Defines `Program` with bytecode, entry points per role, local
types, and metadata. `CodeImage` carries executable data used by the runtime.
`UntrustedImage` represents unverified code pending validation.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

/-! ## Program metadata -/

structure ProgramMeta where
  -- Basic source provenance for auditing.
  name : String
  version : Nat
  sourceHash : UInt64
  footprintSummary : List (Role × List Role) := []
  deriving Repr

/-- Default metadata for generated programs. -/
def ProgramMeta.empty : ProgramMeta :=
  -- Deterministic empty metadata baseline.
  { name := "", version := 0, sourceHash := 0 }

/-! ## Program images -/

abbrev Bytecode (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] :=
  -- Bytecode is just an array of instructions.
  Array (Instr γ ε)

structure Program (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  -- Bytecode and per-role entry points.
  code : Bytecode γ ε
  entryPoints : List (Role × PC)
  localTypes : List (Role × LocalType)
  localTypesR : List (Role × SessionTypes.LocalTypeR.LocalTypeR) := []
  handlerTypes : List (EffectRuntime.EffectAction ε × LocalType)
  metadata : ProgramMeta

structure CodeImage (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  -- Executable program image consumed by runtime loader.
  program : Program γ ε
  globalType : GlobalType

structure RoleCodeImage (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  -- Rust-style map-per-role image view for parity checks and tooling.
  programs : Std.HashMap Role (Bytecode γ ε)
  globalType : GlobalType
  localTypes : Std.HashMap Role SessionTypes.LocalTypeR.LocalTypeR

structure UntrustedImage (γ ε ν : Type u) [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] where
  -- Unverified image pending projection/typing checks.
  program : Program γ ε
  globalType : GlobalType
  signer : VerificationModel.VerifyKey ν
  signature : VerificationModel.Signature ν

/-! ## Compilation pipeline -/

/-- Map roles to their local types in a program image. -/
def programLocalTypes (roles : RoleSet) (types : Role → LocalType) :
    List (Role × LocalType) :=
  -- Preserve role order in the role set.
  roles.map (fun r => (r, types r))

/-! ## Code image construction from LocalTypeR -/

/-! ### Ordering Helpers -/

private def insertRoleOrdered
    (entry : Role × SessionTypes.LocalTypeR.LocalTypeR)
    (acc : List (Role × SessionTypes.LocalTypeR.LocalTypeR)) :
    List (Role × SessionTypes.LocalTypeR.LocalTypeR) :=
  match acc with
  | [] => [entry]
  | x :: xs =>
      if entry.1 <= x.1 then
        entry :: x :: xs
      else
        x :: insertRoleOrdered entry xs

private def sortLocalTypesByRole
    (localTypes : List (Role × SessionTypes.LocalTypeR.LocalTypeR)) :
    List (Role × SessionTypes.LocalTypeR.LocalTypeR) :=
  localTypes.foldl (fun acc entry => insertRoleOrdered entry acc) []

/-! ### Stable Hash Helpers -/

private def mixHash64 (h : UInt64) (n : Nat) : UInt64 :=
  -- Deterministic 64-bit hash mixer (djb2 style).
  ((h <<< 5) + h) + UInt64.ofNat n

private def hashString64 (s : String) : UInt64 :=
  s.toList.foldl (fun h c => mixHash64 h c.toNat) 5381

private def hashCodeImagePayload
    (ordered : List (Role × SessionTypes.LocalTypeR.LocalTypeR))
    (globalType : GlobalType) : UInt64 :=
  let seed := hashString64 (reprStr globalType)
  ordered.foldl
    (fun h entry =>
      let h1 := mixHash64 h entry.1.length
      let h2 := hashString64 entry.1
      let h3 := mixHash64 h1 h2.toNat
      let h4 := hashString64 (reprStr entry.2)
      mixHash64 h3 h4.toNat)
    seed

/-! ### Compile-time Footprint Summary Helpers -/

private def dedupRoles (roles : List Role) : List Role :=
  roles.foldl (fun acc r => if r ∈ acc then acc else acc ++ [r]) []

mutual
  private def localTypeRFootprintRoles : LocalTypeR → List Role
    | .end => []
    | .send partner branches =>
        dedupRoles (partner :: branchFootprintRoles branches)
    | .recv partner branches =>
        dedupRoles (partner :: branchFootprintRoles branches)
    | .mu _ body => localTypeRFootprintRoles body
    | .var _ => []

  private def branchFootprintRoles : List BranchR → List Role
    | [] => []
    | (_, _, cont) :: rest =>
        localTypeRFootprintRoles cont ++ branchFootprintRoles rest
end

private def footprintSummaryOf
    (ordered : List (Role × LocalTypeR)) : List (Role × List Role) :=
  ordered.map (fun p => (p.1, dedupRoles (localTypeRFootprintRoles p.2)))

/-! ### Role Map Builders -/

private def localTypeRMap
    (localTypes : List (Role × SessionTypes.LocalTypeR.LocalTypeR)) :
    Std.HashMap Role SessionTypes.LocalTypeR.LocalTypeR :=
  localTypes.foldl (fun acc entry => acc.insert entry.1 entry.2) {}

private def relocateInstr {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (offset : PC) : Instr γ ε → Instr γ ε
  | .choose chan table =>
      .choose chan (table.map (fun (lbl, pc) => (lbl, offset + pc)))
  | .jump target => .jump (offset + target)
  | .spawn target args => .spawn (offset + target) args
  | instr => instr

private def relocateCode {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (offset : PC) (code : List (Instr γ ε)) : List (Instr γ ε) :=
  code.map (relocateInstr (γ := γ) (ε := ε) offset)

/-! ### Image Constructors -/

/-- Build a CodeImage by compiling LocalTypeR per role and concatenating the bytecode. -/
def CodeImage.fromLocalTypes {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (localTypes : List (Role × SessionTypes.LocalTypeR.LocalTypeR))
    (globalType : GlobalType) : CodeImage γ ε :=
  let ordered := sortLocalTypesByRole localTypes
  let sourceHash := hashCodeImagePayload ordered globalType
  let footprintSummary := footprintSummaryOf ordered
  let step := fun (acc : List (Instr γ ε) × List (Role × PC)) (entry : Role × SessionTypes.LocalTypeR.LocalTypeR) =>
    let (code, entryPoints) := acc
    let (role, lt) := entry
    let startPc := code.length
    let roleCode := compileLocalTypeR (γ:=γ) (ε:=ε) lt
    let code' := code ++ relocateCode (γ := γ) (ε := ε) startPc roleCode
    (code', entryPoints ++ [(role, startPc)])
  let (code, entryPoints) := ordered.foldl step ([], [])
  let localTypes' := ordered.map (fun (r, lt) => (r, localTypeRToLocalType lt))
  { program :=
      { code := code.toArray
      , entryPoints := entryPoints
      , localTypes := localTypes'
      , localTypesR := ordered
      , handlerTypes := []
      , metadata := { ProgramMeta.empty with
          sourceHash := sourceHash
          footprintSummary := footprintSummary } }
  , globalType := globalType }

/-- Rebase executable targets, preserving the original typed action. Nominal
classification is checked after the action model rebases it; a missing or
inconsistent implementation refuses instead of erasing executable semantics. -/
def mapExecutableTargets? {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (target : PC → Option PC) (instruction : Instr γ ε) : Option (Instr γ ε) := do
  match instruction with
  | .choose channel table =>
      let table' ← table.mapM fun entry => do
        let pc ← target entry.2
        pure (entry.1, pc)
      pure (.choose channel table')
  | .jump pc => pure (.jump (← target pc))
  | .spawn pc args => pure (.spawn (← target pc) args)
  | .invoke action =>
      match EffectRuntime.operationAction action with
      | some operation =>
          if (EffectRuntime.commandDeclaration action).isSome || (EffectRuntime.commandCall action).isSome then none
          else do
            let relocated ← operation.mapTargets? target
            let action' ← EffectRuntime.relocateOperation action relocated
            if EffectRuntime.operationAction action' = some relocated ∧
                EffectRuntime.commandDeclaration action' = none ∧ EffectRuntime.commandCall action' = none then
              pure (.invoke action')
            else none
      | none =>
          match EffectRuntime.commandDeclaration action, EffectRuntime.commandCall action with
          | some _, some _ => none
          | _, none => pure instruction
          | none, some call =>
              let ok ← target call.onOk
              let err ← target call.onErr
              let relocated := { call with onOk := ok, onErr := err }
              let action' ← EffectRuntime.relocateCommand action relocated
              if EffectRuntime.commandDeclaration action' = none ∧
                  EffectRuntime.commandCall action' = some relocated then
                pure (.invoke action')
              else none
  | _ => pure instruction

/-- Split the actual executable image at its actual role entries. This never
recompiles communication types: typed actions and their targets must survive.
Malformed entries or cross-role control targets are explicit conversion errors. -/
def CodeImage.toRoleCodeImage {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (image : CodeImage γ ε) : Except String (RoleCodeImage γ ε) := do
  let entries := image.program.entryPoints
  let size := image.program.code.size
  if !entries.isEmpty && !(entries.any fun entry => entry.2 == 0) then
    throw "executable image has no initial role entry"
  if entries.isEmpty && size != 0 then throw "executable image has no role entries"
  let programs ← entries.foldlM (fun acc entry => do
    if entry.2 ≥ size || (entries.filter fun other => other.1 == entry.1).length != 1 ||
        (entries.filter fun other => other.2 == entry.2).length != 1 then
      throw "executable image has ambiguous or invalid role entries"
    let limit := entries.foldl (fun stop other =>
      if entry.2 < other.2 then min stop other.2 else stop) size
    let target := fun pc => if entry.2 ≤ pc ∧ pc < limit then some (pc - entry.2) else none
    let chunk := (image.program.code.toList.drop entry.2).take (limit - entry.2)
    let code ← match chunk.mapM (mapExecutableTargets? (γ := γ) (ε := ε) target) with
      | some code => pure code
      | none => throw "executable role target or typed action cannot be preserved"
    pure (acc.insert entry.1 code.toArray)) ({} : Std.HashMap Role (Bytecode γ ε))
  pure { programs := programs, globalType := image.globalType,
    localTypes := localTypeRMap image.program.localTypesR }

/-- Assemble actual per-role executable programs. Nominal action relocation is
supplied by its typed action model and checked against the exact descriptor.
This conversion does not issue an operation, endpoint or host owner. -/
def RoleCodeImage.toCodeImage {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (image : RoleCodeImage γ ε) (roles : List Role) : Except String (CodeImage γ ε) := do
  if roles.length != image.programs.size || roles.eraseDups.length != roles.length then
    throw "role order does not name each executable program exactly once"
  let (code, entries) ← roles.foldlM (fun (acc : List (Instr γ ε) × List (Role × PC)) role => do
    let original ← match image.programs[role]? with
      | some code => pure code
      | none => throw "missing executable role program"
    if original.isEmpty then throw "empty executable role program"
    let offset := acc.1.length
    let target := fun pc => if pc < original.size then some (offset + pc) else none
    let relocated ← match original.toList.mapM (mapExecutableTargets? (γ := γ) (ε := ε) target) with
      | some code => pure code
      | none => throw "executable role target or typed action cannot be relocated"
    pure (acc.1 ++ relocated, acc.2 ++ [(role, offset)])) ([], [])
  let locals ← roles.mapM fun role => match image.localTypes[role]? with
    | some local => pure (role, local)
    | none => throw "missing executable role local type"
  pure { program := { code := code.toArray, entryPoints := entries,
      localTypes := locals.map fun entry => (entry.1, localTypeRToLocalType entry.2),
      localTypesR := locals, handlerTypes := [], metadata := ProgramMeta.empty },
    globalType := image.globalType }

/-! ## Nominal command image admission
Classification inspects typed EffectRuntime actions; no operation-name string is
interpreted as an instruction or as live authority. Legacy action models leave
both classifiers None and preserve their original image admission. -/
/-- Exact supported terminal communication plus explicit source resolution. -/
def nominalTerminalBranch {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (code : Bytecode γ ε) (limit target : Nat) (operation : String) : Bool :=
  let haltAt := fun pc => decide (pc < limit) && match code[pc]? with
    | some .halt => true | _ => false
  let resolutionAt := fun pc => match code[pc]? with
    | some (.invoke action) => match EffectRuntime.operationAction action with
      | some (.resolve _ (.timeout _)) => false
      | some (.resolve name _) => name == operation && haltAt (pc + 1)
      | _ => false
    | _ => false
  match code[target]? with
  | some (.offer 0 _) =>
      haltAt (target + 1) || resolutionAt (target + 1) ||
      (match code[target + 1]? with
        | some (.invoke action) => match EffectRuntime.operationAction action with
          | some (.await name) => name == operation && resolutionAt (target + 2)
          | _ => false
        | _ => false)
  | _ => false

private def priorSourceDeclaration {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (code : Bytecode γ ε) (role : Role) (pc : Nat) (name : String) :
    Option Runtime.ProtocolMachine.Model.SourceOperationDeclaration :=
  (code.toList.take pc).findSome? (fun instruction => match instruction with
    | .invoke action => match EffectRuntime.operationAction action with
      | some (.begin declaration) =>
          if declaration.role == role && declaration.name == name then some declaration else none
      | _ => none
    | _ => none)

private def sourceActionShapeValid {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (code : Bytecode γ ε) (role : Role) (limit pc : Nat)
    (action : Runtime.ProtocolMachine.Model.OperationAction) : Bool :=
  match action with
  | .begin declaration =>
      let hasTerminal := ((code.toList.drop (pc + 1)).take (limit - (pc + 1))).any (fun instruction =>
        match instruction with
        | .invoke action => match EffectRuntime.operationAction action with
          | some (.resolve name _) | some (.invalidate name) => name == declaration.name
          | _ => false
        | _ => false)
      declaration.supported && declaration.role == role && hasTerminal &&
      declaration.requiredChildren.all (fun slot =>
        decide (pc < slot.pc ∧ slot.pc < limit ∧ slot.call.enclosingOperation = declaration.name ∧
          slot.call.role = role ∧ slot.call.agreementProfile = declaration.agreementProfile ∧
          slot.call.progressContract = declaration.progressContract ∧
          slot.call.progressWindow = declaration.progressWindow ∧ slot.call.budgetTicks = declaration.budgetTicks) &&
        (declaration.requiredChildren.filter (fun other => other.pc == slot.pc)).length == 1 &&
        match code[slot.pc]? with
        | some (.invoke actual) => decide (EffectRuntime.commandCall actual = some slot.call)
        | _ => false)
  | .resolve _ (.timeout _) | .unsupportedComposition => false
  | .await name | .resolve name _ | .invalidate name =>
      (priorSourceDeclaration code role pc name).isSome

private def scanNominalProgram {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (code : Bytecode γ ε) (role : Role) (limit : Nat)
    (rest : List (Instr γ ε)) (pc : Nat)
    (executable : Bool) (declarations : List Runtime.ProtocolMachine.Model.NominalCommandDeclaration) : Bool :=
  match rest with
  | [] => true
  | instruction :: tail =>
      let next := fun executable declarations => scanNominalProgram code role limit tail (pc + 1) executable declarations
      match instruction with
      | .invoke action =>
          match EffectRuntime.operationAction action with
          | some operation =>
              (EffectRuntime.commandDeclaration action).isNone && (EffectRuntime.commandCall action).isNone &&
                sourceActionShapeValid code role limit pc operation && next true declarations
          | none =>
              match EffectRuntime.commandDeclaration action, EffectRuntime.commandCall action with
              | some declaration, none =>
                  !executable && declaration.readinessWellFormed && !declaration.interfaceName.isEmpty && !declaration.operationName.isEmpty &&
                    !(declarations.any fun prior => prior.interfaceName == declaration.interfaceName && prior.operationName == declaration.operationName) &&
                    next false (declarations ++ [declaration])
              | none, some call =>
                  let terminal := fun target => nominalTerminalBranch code limit target call.enclosingOperation
                  let sourceChild := match priorSourceDeclaration code role pc call.enclosingOperation with
                    | none => true
                    | some declaration => declaration.requiredChildren.any (fun slot => decide (slot.pc = pc ∧ slot.call = call))
                  decide (call.role = role ∧ call.declaration ∈ declarations ∧ call.result > 0 ∧ call.budgetTicks > 0 ∧
                    call.onOk > pc ∧ call.onErr > pc ∧ call.onOk ≠ call.onErr ∧
                    call.enclosingOperation ≠ "" ∧ call.progressContract ≠ "" ∧ call.progressWindow ≠ "" ∧
                    call.agreementProfile.profileName ≠ "" ∧ call.agreementProfile.visibility = .immediate ∧
                    call.agreementProfile.rule = .noAgreement ∧ call.agreementProfile.usableAt = .none ∧
                    call.agreementProfile.finalizedAt = .none ∧ call.agreementProfile.requiredEvidenceKind = .witness) &&
                    sourceChild && terminal call.onOk && terminal call.onErr && next true declarations
              | some _, some _ => false
              | none, none => next true declarations
      | _ => next true declarations

/-- Validate static nominal declarations and terminal typed-result continuations.
This grants no issued Rust host ownership handle. -/
def nominalProgramValid {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (program : Program γ ε) : Bool :=
  let entries := program.entryPoints
  let validEntries := entries.all fun entry =>
    decide (entry.2 < program.code.size) &&
      decide ((entries.filter fun other => other.1 == entry.1).length = 1) &&
      decide ((entries.filter fun other => other.2 == entry.2).length = 1)
  let validChunks := entries.all fun entry =>
    let limit := entries.foldl (fun stop other =>
      if entry.2 < other.2 then min stop other.2 else stop) program.code.size
    let chunk := (program.code.toList.drop entry.2).take (limit - entry.2)
    scanNominalProgram program.code entry.1 limit chunk entry.2 false []
  -- Empty communication images keep their previous admission. A nominal action
  -- without an actual role entry cannot acquire a declaration from another role.
  let classified := program.code.toList.any fun instruction => match instruction with
    | .invoke action => (EffectRuntime.commandDeclaration action).isSome ||
        (EffectRuntime.commandCall action).isSome || (EffectRuntime.operationAction action).isSome
    | _ => false
  !classified || (validEntries && !entries.isEmpty &&
    entries.any (fun entry => entry.2 == 0) && validChunks)
