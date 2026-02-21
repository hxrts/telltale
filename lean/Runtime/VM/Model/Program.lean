import Runtime.VM.Model.Core
import Runtime.VM.Model.TypeClasses
import Runtime.VM.Model.CompileLocalTypeR
import SessionTypes.LocalTypeR

/-! # Program Images and Compilation

`Program`, `CodeImage`, and `UntrustedImage`, the program representation that the
VM loads and executes. A `Program` is bytecode plus per-role entry points, local types,
handler types, and source metadata. A `CodeImage` bundles executable program payload with
its global type. An
`UntrustedImage` is an unverified program pending signature and typing checks, used by
the code loading pipeline (`runtime.md` §10).
-/

/-
The Problem. The VM needs a program representation that bundles bytecode with type
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

private def roleProgramMap {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (localTypes : List (Role × SessionTypes.LocalTypeR.LocalTypeR)) :
    Std.HashMap Role (Bytecode γ ε) :=
  localTypes.foldl
    (fun acc entry => acc.insert entry.1 (compileLocalTypeR (γ := γ) (ε := ε) entry.2).toArray)
    {}

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
    let code' := code ++ compileLocalTypeR (γ:=γ) (ε:=ε) lt
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

def CodeImage.toRoleCodeImage {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (image : CodeImage γ ε) : RoleCodeImage γ ε :=
  { programs := roleProgramMap (γ := γ) (ε := ε) image.program.localTypesR
  , globalType := image.globalType
  , localTypes := localTypeRMap image.program.localTypesR }
