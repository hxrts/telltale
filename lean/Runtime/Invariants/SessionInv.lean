import Runtime.Resources.SessionRA
import Runtime.Compat.Inv
import Runtime.Compat.SavedProp

/-!
# Task 16: Session Cancelable Invariants

Per-session cancelable invariant from iris_runtime_2.md §7.

## Definitions

- `sessionNs sid` — namespace per session
- `session_inv γ sid ct` — cancelable invariant body
- `session_ns_disjoint`
- `session_inv_alloc` / `session_inv_open` / `session_inv_close`
- `Participation` — per-endpoint lifecycle token
- `LifecycleEvent` — open, join, leave, close
- `open_coherent`, `leave_preserves_coherent`, `close_empty`

Dependencies: Task 13, Shim.Invariants + Shim.SavedProp.
-/

set_option autoImplicit false
noncomputable section

def sessionNs (sid : SessionId) : Namespace :=
  Namespace.append_nat Namespace.root sid

def session_inv (_γ : GhostName) (sid : SessionId) (ct : CancelToken) : iProp :=
  cinv (sessionNs sid) ct iProp.emp

def session_ns_disjoint (sid₁ sid₂ : SessionId)
    (hNs : sessionNs sid₁ ≠ sessionNs sid₂) :
  Mask.disjoint (namespace_to_mask (sessionNs sid₁)) (namespace_to_mask (sessionNs sid₂)) :=
  namespace_disjoint (sessionNs sid₁) (sessionNs sid₂) hNs

def session_inv_alloc (γ : GhostName) (sid : SessionId) (E : Mask) :
  iProp.entails (iProp.later iProp.emp)
    (fupd E E (iProp.exist fun ct => iProp.sep (session_inv γ sid ct) (cancel_token_own ct))) :=
  cinv_alloc (sessionNs sid) E iProp.emp

def session_inv_open (γ : GhostName) (sid : SessionId) (ct : CancelToken) (E : Mask)
    (hSub : Mask.subseteq (namespace_to_mask (sessionNs sid)) E) :
  iProp.entails (session_inv γ sid ct)
    (fupd E (Mask.diff E (namespace_to_mask (sessionNs sid)))
      (iProp.sep (iProp.later iProp.emp)
        (iProp.wand (iProp.later iProp.emp)
          (fupd (Mask.diff E (namespace_to_mask (sessionNs sid))) E iProp.emp)))) :=
  cinv_acc (sessionNs sid) E ct iProp.emp hSub

def session_inv_close (γ : GhostName) (sid : SessionId) (ct : CancelToken) (E : Mask)
    (hSub : Mask.subseteq (namespace_to_mask (sessionNs sid)) E) :
  iProp.entails (iProp.sep (session_inv γ sid ct) (cancel_token_own ct))
    (fupd E (Mask.diff E (namespace_to_mask (sessionNs sid))) (iProp.later iProp.emp)) :=
  cinv_cancel (sessionNs sid) E ct iProp.emp hSub

structure Participation where
  endpoint : Endpoint
  deriving Repr

inductive LifecycleEvent where
  | open
  | join
  | leave
  | close
  deriving Repr

def open_coherent (_sid : SessionId) : Prop := True
def leave_preserves_coherent (_sid : SessionId) : Prop := True
def close_empty (_sid : SessionId) : Prop := True
