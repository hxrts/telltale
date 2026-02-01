import Std
import Runtime.VM.TypeClasses

/-!
# Core VM Types

Scalar aliases (`Reg`, `PC`, `CoroutineId`, etc.), the `Expr` handle for coroutine
expressions, and the `Instr` bytecode instruction set. Instructions are parameterized
by the guard layer `γ` and effect model `ε` so that domain-specific guard and effect
actions appear directly in the bytecode.

The instruction set is organized into paired groups that mirror the acquire/interact/release
pattern described in `runtime.md` §3: communication (send/recv, offer/choose), resources
(acquire/release), sessions (open/close), speculation (fork/join/abort), ownership and
knowledge (transfer, tag/check), and control flow (loadImm, mov, jmp, spawn, yield, halt).
-/

set_option autoImplicit false

universe u

/-! ## Core VM scalars -/

abbrev Reg := Nat
abbrev Addr := Nat
abbrev PC := Nat
abbrev CoroutineId := Nat
abbrev HandlerId := Nat
abbrev GuardChainId := Nat
abbrev GhostSessionId := Nat
abbrev Imm := Value

structure Expr where
  -- Stable handle for a coroutine expression.
  cid : CoroutineId
  halted : Bool
  deriving Repr, DecidableEq

/-! ## Bytecode instructions -/

inductive Instr (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
  -- Bytecode instruction set.
  | send (chan val : Reg)
  | recv (chan dst : Reg)
  | offer (chan : Reg) (label : Label)
  | choose (chan : Reg) (table : List (Label × PC))
  | acquire (layer : γ) (dst : Reg)
  | release (layer : γ) (evidence : Reg)
  | invoke (action : EffectModel.EffectAction ε)
  | open (roles : RoleSet) (localTypes : List (Role × LocalType))
      (handlers : List (Edge × HandlerId)) (dsts : List (Role × Reg))
  | close (session : Reg)
  | fork (sid : Reg)
  | join
  | abort
  | transfer (endpoint : Reg) (targetCoro : Reg) (bundle : Reg)
  | tag (fact : Reg) (dst : Reg)
  | check (knowledge : Reg) (target : Reg) (dst : Reg)
  | loadImm (dst : Reg) (v : Imm)
  | mov (dst src : Reg)
  | jmp (target : PC)
  | spawn (target : PC) (args : List Reg)
  | yield
  | halt

abbrev RegFile := Array Value
