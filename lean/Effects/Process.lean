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
- `G`: type environment mapping endpoints to local types
- `D`: trace environment mapping edges to in-flight message types
- `nextSid`: next fresh session ID
-/
structure Config where
  proc : Process
  store : Store
  bufs : Buffers
  G : GEnv
  D : DEnv
  nextSid : SessionId

namespace Config

/-- Initial configuration with just a process and empty environments. -/
def init (P : Process) : Config :=
  { proc := P, store := [], bufs := [], G := [], D := [], nextSid := 0 }

/-- Initial configuration with type environments. -/
def initWithEnv (P : Process) (G : GEnv) (D : DEnv) : Config :=
  { proc := P, store := [], bufs := [], G := G, D := D, nextSid := 0 }

/-- Check if configuration has terminated. -/
def isTerminated (C : Config) : Bool :=
  C.proc.isSkip

end Config

/-! ## Configuration Update Helpers -/

/-- Update configuration after a send on edge e from endpoint ep.
    - Process becomes skip
    - Buffer at edge e gets v enqueued
    - G[ep] advances from `send target T L` to `L`
    - D[e] grows by appending T -/
def sendStep (C : Config) (ep : Endpoint) (e : Edge) (v : Value) (T : ValType) (L : LocalType) : Config :=
  { C with
    proc := .skip
    bufs := enqueueBuf C.bufs e v
    G := updateG C.G ep L
    D := updateD C.D e (lookupD C.D e ++ [T]) }

/-- Update configuration after a receive on edge e at endpoint ep.
    - Process becomes skip
    - Variable x gets value v
    - Buffer at edge e loses head element
    - G[ep] advances from `recv source T L` to `L`
    - D[e] shrinks by removing head -/
def recvStep (C : Config) (ep : Endpoint) (e : Edge) (x : Var) (v : Value) (L : LocalType) : Config :=
  match dequeueBuf C.bufs e with
  | some (bufs', _) =>
    { C with
      proc := .skip
      store := updateStr C.store x v
      bufs := bufs'
      G := updateG C.G ep L
      D := updateD C.D e (lookupD C.D e).tail }
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
