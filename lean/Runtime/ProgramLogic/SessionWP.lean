import Runtime.ProgramLogic.LanguageInstance
import Runtime.Invariants.SessionInv
import Runtime.ProgramLogic.GhostState
import Runtime.ProgramLogic.WPPair
import IrisExtractionInstance

/- 
The Problem. Provide uniform WP rules for VM instructions without repeating
the same invariant open/close structure across each proof.

Solution Structure. Delegate each WP rule to the generic `wp_pair`
combinator and expose the derived rules as the public API.
-/

/-! # Task 19: Session WP Rules

Weakest precondition rules for each bytecode instruction from iris_runtime_2.md §7.

## Rules

- `wp_send`, `wp_receive`, `wp_offer`, `wp_choose`
- `wp_open`, `wp_close`
- `wp_acquire`, `wp_release`
- `wp_invoke`, `wp_fork`, `wp_join`, `wp_abort`
- `wp_transfer`, `wp_tag`, `wp_check`
- `wp_set`, `wp_move`, `wp_jump`, `wp_spawn`, `wp_yield`, `wp_halt`

Dependencies: Task 12, Task 16, Shim.Invariants + Shim.WeakestPre.
-/

set_option autoImplicit false
section

/-! ## Core WP Rules -/

universe u

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
variable [Telltale.TelltaleIris]
variable [GhostMapSlot Unit]
variable [GhostMapSlot Nat]
variable [GhostMapSlot LocalType]

def wp_send (γn : GhostName) (sid : SessionId) (ct : CancelToken)
    (e : Endpoint) (L : LocalType) : iProp :=
  -- Send requires the session invariant and endpoint ownership.
  iProp.sep (session_inv γn sid ct) (endpoint_frag γn e L)

def wp_send_delegation (γn : GhostName) (sid : SessionId) (ct : CancelToken)
    (b : ResourceBundle γ ε) : iProp :=
  -- Delegating send requires ordinary send resources plus a transferable bundle.
  iProp.sep (wp_send γn sid ct b.endpoint b.localType) (bundle_owns γn b)

def wp_receive : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (receivePair (γ:=γ) (ε:=ε))

def wp_receive_delegation (γn : GhostName) (sid : SessionId) (ct : CancelToken)
    (b : ResourceBundle γ ε) : iProp :=
  -- Delegating receive consumes from the session invariant and installs bundle ownership.
  iProp.sep (session_inv γn sid ct) (bundle_owns γn b)

def wp_offer : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (offerPair (γ:=γ) (ε:=ε))

def wp_choose : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (choosePair (γ:=γ) (ε:=ε))

def wp_open : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (openPair (γ:=γ) (ε:=ε))

def wp_close (γn : GhostName) (sid : SessionId) (ct : CancelToken) : iProp :=
  -- Close requires the cancel token and the session invariant.
  iProp.sep (session_inv γn sid ct) (cancel_token_own ct)

def wp_acquire (layer : γ) : iProp :=
  -- Acquire WP: parameterized by the guard layer.
  wp_pair (acquirePair (γ:=γ) (ε:=ε) layer)

def wp_release (layer : γ) : iProp :=
  -- Release WP: parameterized by the guard layer.
  wp_pair (releasePair (γ:=γ) (ε:=ε) layer)

def wp_invoke (action : EffectRuntime.EffectAction ε) : iProp :=
  -- Invoke WP: parameterized by the effect action.
  wp_pair (invokePair (γ:=γ) (ε:=ε) action)

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

def wp_set : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (setPair (γ:=γ) (ε:=ε))

def wp_move : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (movePair (γ:=γ) (ε:=ε))

def wp_jump : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (jumpPair (γ:=γ) (ε:=ε))

def wp_spawn : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (spawnPair (γ:=γ) (ε:=ε))

def wp_yield : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (yieldPair (γ:=γ) (ε:=ε))

def wp_halt : iProp :=
  -- WP rule derived from the generic pair rule.
  wp_pair (haltPair (γ:=γ) (ε:=ε))
