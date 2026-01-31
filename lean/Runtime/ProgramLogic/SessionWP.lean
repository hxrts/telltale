import Runtime.VM.LanguageInstance
import Runtime.Invariants.SessionInv
import Runtime.ProgramLogic.WPPair
import Runtime.Compat.Inv
import Runtime.Compat.WP

/- 
The Problem. Provide uniform WP rules for VM instructions without repeating
the same invariant open/close structure across each proof.

Solution Structure. Delegate each WP rule to the generic `wp_pair`
combinator and expose the derived rules as the public API.
-/

/-!
# Task 19: Session WP Rules

Weakest precondition rules for each bytecode instruction from iris_runtime_2.md §7.

## Rules

- `wp_send`, `wp_recv`, `wp_offer`, `wp_choose`
- `wp_open`, `wp_close`
- `wp_acquire`, `wp_release`
- `wp_invoke`, `wp_fork`, `wp_join`, `wp_abort`
- `wp_transfer`, `wp_tag`, `wp_check`
- `wp_loadImm`, `wp_mov`, `wp_jmp`, `wp_spawn`, `wp_yield`, `wp_halt`

Dependencies: Task 12, Task 16, Shim.Invariants + Shim.WeakestPre.
-/

set_option autoImplicit false
noncomputable section

universe u

variable {γ ε : Type u} [GuardLayer γ] [EffectModel ε]

def wp_send : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (sendPair (γ:=γ) (ε:=ε))

def wp_recv : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (recvPair (γ:=γ) (ε:=ε))

def wp_offer : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (offerPair (γ:=γ) (ε:=ε))

def wp_choose : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (choosePair (γ:=γ) (ε:=ε))

def wp_open : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (openPair (γ:=γ) (ε:=ε))

def wp_close : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (closePair (γ:=γ) (ε:=ε))

def wp_acquire : iProp :=
  -- Acquire WP: abstract over the guard layer.
  iProp.exist (fun layer => wp_pair (acquirePair (γ:=γ) (ε:=ε) layer))

def wp_release : iProp :=
  -- Release WP: abstract over the guard layer.
  iProp.exist (fun layer => wp_pair (releasePair (γ:=γ) (ε:=ε) layer))

def wp_invoke : iProp :=
  -- Invoke WP: abstract over effect actions.
  iProp.exist (fun action => wp_pair (invokePair (γ:=γ) (ε:=ε) action))

def wp_fork : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (forkPair (γ:=γ) (ε:=ε))

def wp_join : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (joinPair (γ:=γ) (ε:=ε))

def wp_abort : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (abortPair (γ:=γ) (ε:=ε))

def wp_transfer : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (transferPair (γ:=γ) (ε:=ε))

def wp_tag : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (tagPair (γ:=γ) (ε:=ε))

def wp_check : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (checkPair (γ:=γ) (ε:=ε))

def wp_loadImm : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (loadImmPair (γ:=γ) (ε:=ε))

def wp_mov : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (movPair (γ:=γ) (ε:=ε))

def wp_jmp : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (jmpPair (γ:=γ) (ε:=ε))

def wp_spawn : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (spawnPair (γ:=γ) (ε:=ε))

def wp_yield : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (yieldPair (γ:=γ) (ε:=ε))

def wp_halt : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (haltPair (γ:=γ) (ε:=ε))
