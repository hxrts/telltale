import Runtime.VM.Model.Core
import Runtime.IrisBridge

/- 
The Problem. Many instruction WP rules share the same acquire/interact/release
shape, but the proofs are duplicated across each concrete instruction.

Solution Structure. Introduce an `InstrPair` abstraction and a generic
`wp_pair` rule that concrete WP rules can reuse.
-/

set_option autoImplicit false
section

universe u

variable [Telltale.TelltaleIris]

/-! ## Instruction pairs -/

structure InstrPair (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  -- Common shape for acquire/interact/release reasoning.
  instr : Instr γ ε
  openCtx : iProp
  interact : iProp
  closeCtx : iProp
  pre : iProp
  post : iProp

def mkPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (instr : Instr γ ε) : InstrPair γ ε :=
  -- Build a placeholder instruction pair for refactoring.
  { instr := instr
  , openCtx := iProp.emp
  , interact := iProp.emp
  , closeCtx := iProp.emp
  , pre := iProp.emp
  , post := iProp.emp }

def wp_pair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (_p : InstrPair γ ε) : iProp :=
  -- Generic WP rule for instruction pairs (placeholder).
  iProp.emp

/-! ## Concrete pair instances -/

def sendPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `send`.
  mkPair (.send 0 0)

def receivePair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `receive`.
  mkPair (.receive 0 0)

def offerPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `offer`.
  mkPair (.offer 0 "")

def choosePair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `choose`.
  mkPair (.choose 0 [])

def openPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `open`.
  mkPair (.open [] [] [] [])

def closePair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `close`.
  mkPair (.close 0)

def acquirePair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (layer : γ) : InstrPair γ ε :=
  -- Pair wrapper for `acquire`.
  mkPair (.acquire layer 0)

def releasePair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (layer : γ) : InstrPair γ ε :=
  -- Pair wrapper for `release`.
  mkPair (.release layer 0)

def invokePair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (action : EffectRuntime.EffectAction ε) : InstrPair γ ε :=
  -- Pair wrapper for `invoke`.
  mkPair (.invoke action)

def transferPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `transfer`.
  mkPair (.transfer 0 0 0)

def tagPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `tag`.
  mkPair (.tag 0 0)

def checkPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `check`.
  mkPair (.check 0 0 0)

def forkPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `fork`.
  mkPair (.fork 0)

def joinPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `join`.
  mkPair .join

def abortPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `abort`.
  mkPair .abort

def setPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `set`.
  mkPair (.set 0 .unit)

def movePair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `move`.
  mkPair (.move 0 0)

def jumpPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `jump`.
  mkPair (.jump 0)

def spawnPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `spawn`.
  mkPair (.spawn 0 [])

def yieldPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `yield`.
  mkPair .yield

def haltPair {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] : InstrPair γ ε :=
  -- Pair wrapper for `halt`.
  mkPair .halt
