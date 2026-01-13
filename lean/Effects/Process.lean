import Effects.Coherence

/-!
# MPST Process Language

This module defines the process language for multiparty session types.

The process language is similar to the binary session types language,
but operations are multiparty-aware:
- `send k x`: send value in x through channel k (target role is in the type)
- `recv k x`: receive into x through channel k (source role is in the type)
- `select k ℓ`: select label ℓ on channel k
- `branch k bs`: branch on incoming label from channel k

Channels carry `Endpoint = (SessionId, Role)` pairs, and the local type
determines which role we communicate with.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Process language for MPST.

- `skip`: terminated process
- `seq P Q`: sequential composition
- `par P Q`: parallel composition
- `send k x`: send value in variable x through channel k
- `recv k x`: receive a value into variable x through channel k
- `select k ℓ`: send label ℓ through channel k
- `branch k bs`: receive a label through k and branch to corresponding process
- `newSession roles f`: create a new session with given roles,
                         binding channel variables via f
- `assign x v`: assign a non-linear value to variable x
-/
inductive Process where
  | skip : Process
  | seq : Process → Process → Process
  | par : Process → Process → Process
  | send : Var → Var → Process  -- send k x: send x through channel k
  | recv : Var → Var → Process  -- recv k x: receive into x through channel k
  | select : Var → Label → Process  -- select k ℓ
  | branch : Var → List (Label × Process) → Process  -- branch k [(ℓ₁, P₁), ...]
  | newSession : RoleSet → (Role → Var) → Process → Process
  | assign : Var → Value → Process

namespace Process

/-- Check if a process is terminated. -/
def isSkip : Process → Bool
  | .skip => true
  | _ => false

/-- Get immediate free variables in a process (non-recursive for branches). -/
def freeVarsImmediate : Process → List Var
  | .skip => []
  | .seq P Q => P.freeVarsImmediate ++ Q.freeVarsImmediate
  | .par P Q => P.freeVarsImmediate ++ Q.freeVarsImmediate
  | .send k x => [k, x]
  | .recv k x => [k]  -- x is bound
  | .select k _ => [k]
  | .branch k _ => [k]  -- simplified: don't recurse into branch processes
  | .newSession _ _ P => P.freeVarsImmediate  -- f's range is bound
  | .assign _ _ => []

end Process

/-! ## Runtime Configuration -/

/-- Runtime configuration for MPST.

- `proc`: the process being executed
- `store`: variable store
- `bufs`: per-edge message buffers
- `nextSid`: next fresh session ID
-/
structure Config where
  proc : Process
  store : Store
  bufs : Buffers
  nextSid : SessionId

namespace Config

/-- Initial configuration with just a process. -/
def init (P : Process) : Config :=
  { proc := P, store := [], bufs := [], nextSid := 0 }

/-- Check if configuration has terminated. -/
def isTerminated (C : Config) : Bool :=
  C.proc.isSkip

end Config

/-! ## Configuration Update Helpers -/

/-- Update configuration after a send on edge e. -/
def sendStep (C : Config) (e : Edge) (v : Value) : Config :=
  { C with
    proc := .skip
    bufs := enqueueBuf C.bufs e v }

/-- Update configuration after a receive on edge e. -/
def recvStep (C : Config) (e : Edge) (x : Var) (v : Value) : Config :=
  match dequeueBuf C.bufs e with
  | some (bufs', _) =>
    { C with
      proc := .skip
      store := updateStr C.store x v
      bufs := bufs' }
  | none => C  -- shouldn't happen if well-typed

/-- Update configuration after creating a new session. -/
def newSessionStep (C : Config) (roles : RoleSet) (f : Role → Var) : Config :=
  let sid := C.nextSid
  let store' := roles.foldl (fun s r => updateStr s (f r) (.chan ⟨sid, r⟩)) C.store
  let bufs' := initBuffers sid roles ++ C.bufs
  { C with
    proc := .skip
    store := store'
    bufs := bufs'
    nextSid := sid + 1 }

end
