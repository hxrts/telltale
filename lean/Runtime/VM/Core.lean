import Std
import Runtime.VM.TypeClasses

/-
The Problem. The VM needs a core set of instruction and register types that
can be shared across configuration, semantics, and proofs.

Solution Structure. Define scalar aliases, the expression handle, and the
bytecode instruction set parameterized by guard/effect models.
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
  -- Communication
  | send (chan val : Reg)
  | recv (chan dst : Reg)
  | offer (chan : Reg) (label : Label)
  | choose (chan : Reg) (table : List (Label × PC))
  -- Resources
  | acquire (layer : γ) (dst : Reg)
  | release (layer : γ) (evidence : Reg)
  -- Effects
  | invoke (action : EffectModel.EffectAction ε)
  -- Sessions
  | open (roles : RoleSet) (localTypes : List (Role × LocalType))
      (handlers : List (Edge × HandlerId)) (dsts : List (Role × Reg))
  | close (session : Reg)
  -- Speculation
  | fork (sid : Reg)
  | join
  | abort
  -- Ownership and knowledge
  | transfer (endpoint : Reg) (targetCoro : Reg) (bundle : Reg)
  | tag (fact : Reg) (dst : Reg)
  | check (knowledge : Reg) (target : Reg) (dst : Reg)
  -- Control
  | loadImm (dst : Reg) (v : Imm)
  | mov (dst src : Reg)
  | jmp (target : PC)
  | spawn (target : PC) (args : List Reg)
  | yield
  | halt

abbrev RegFile := Array Value
