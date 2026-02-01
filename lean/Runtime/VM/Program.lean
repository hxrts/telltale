import Runtime.VM.Core
import Runtime.VM.TypeClasses
import Protocol.Process

/-
The Problem. The VM needs a program image format and a compiler stub that
connects high-level processes to bytecode programs.

Solution Structure. Define program metadata, program images, and a minimal
`compile` placeholder plus refinement statement.
-/

set_option autoImplicit false

universe u

/-! ## Program metadata -/

structure ProgramMeta where
  -- Basic source provenance for auditing.
  name : String
  version : Nat
  sourceHash : UInt64
  deriving Repr

/-- Default metadata for stub programs. -/
def ProgramMeta.empty : ProgramMeta :=
  -- Use empty metadata until a real compiler is wired in.
  { name := "", version := 0, sourceHash := 0 }

/-! ## Program images -/

abbrev Bytecode (γ ε : Type u) [GuardLayer γ] [EffectModel ε] :=
  -- Bytecode is just an array of instructions.
  Array (Instr γ ε)

structure Program (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
  -- Bytecode and per-role entry points.
  code : Bytecode γ ε
  entryPoints : List (Role × PC)
  localTypes : List (Role × LocalType)
  handlerTypes : List (EffectModel.EffectAction ε × LocalType)
  metadata : ProgramMeta

structure CodeImage (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
  -- Verified program image with global typing evidence.
  program : Program γ ε
  globalType : GlobalType
  wfBlind : Prop
  projectionCorrect : Prop

structure UntrustedImage (γ ε ν : Type u) [GuardLayer γ] [EffectModel ε]
    [VerificationModel ν] where
  -- Unverified image pending projection/typing checks.
  program : Program γ ε
  globalType : GlobalType
  signer : VerificationModel.VerifyKey ν
  signature : VerificationModel.Signature ν

/-! ## Compilation scaffold -/

/-- Map roles to their local types in a program image. -/
def programLocalTypes (roles : RoleSet) (types : Role → LocalType) :
    List (Role × LocalType) :=
  -- Preserve role order in the role set.
  roles.map (fun r => (r, types r))

/-- Compile a process into a program (stub). -/
def compile {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (p : Process) (roles : RoleSet) (types : Role → LocalType)
    (chain : GuardChain γ) : Program γ ε :=
  -- Placeholder compiler: emit empty code with trivial metadata.
  let _ := p
  let _ := chain
  { code := #[],
    entryPoints := roles.map (fun r => (r, 0)),
    localTypes := programLocalTypes roles types,
    handlerTypes := [],
    metadata := ProgramMeta.empty }
