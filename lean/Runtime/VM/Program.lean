import Runtime.VM.Core
import Runtime.VM.TypeClasses
import Protocol.Process

/-!
# Program Images and Compilation

`Program`, `CodeImage`, and `UntrustedImage`, the program representation that the
VM loads and executes. A `Program` is bytecode plus per-role entry points, local types,
handler types, and source metadata. A `CodeImage` bundles a program with its global type
and well-formedness/projection-correctness evidence (currently `Prop` stubs). An
`UntrustedImage` is an unverified program pending signature and typing checks, used by
the code loading pipeline (`runtime.md` §10).

The `compile` function is a V1 stub that translates a `Process` (from `Protocol.Process`)
into a flat bytecode block. It maps variables to registers by name length and emits a
single basic block followed by `halt`. A real compiler would produce optimized bytecode
with proper register allocation and branch targets.
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

def regOf (v : Var) : Reg :=
  -- V1 register mapping: deterministic by variable name length.
  v.length

def compileBlock {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (p : Process) : List (Instr γ ε) :=
  -- Compile a single process into a flat instruction list.
  match p with
  | .skip => []
  | .assign x v => [Instr.loadImm (regOf x) v]
  | .send k x => [Instr.send (regOf k) (regOf x)]
  | .recv k x => [Instr.recv (regOf k) (regOf x)]
  | .select k lbl => [Instr.offer (regOf k) lbl]
  | .branch k branches =>
      let table := branches.map (fun b => (b.1, 0))
      [Instr.choose (regOf k) table]
  | .seq p₁ p₂ => compileBlock p₁ ++ compileBlock p₂
  | .par p₁ p₂ => compileBlock p₁ ++ compileBlock p₂
  | .newSession _ _ p' => compileBlock p'

/-- Compile a process into a program (stub). -/
def compile {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (p : Process) (roles : RoleSet) (types : Role → LocalType)
    (chain : GuardChain γ) : Program γ ε :=
  -- V1 compiler: emit a single-process bytecode block and halt.
  let _ := p
  let _ := chain
  let code := (compileBlock (γ:=γ) (ε:=ε) p) ++ [Instr.halt]
  { code := code.toArray,
    entryPoints := roles.map (fun r => (r, 0)),
    localTypes := programLocalTypes roles types,
    handlerTypes := [],
    metadata := ProgramMeta.empty }
