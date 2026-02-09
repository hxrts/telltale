import Runtime.VM.Model.Core

/-!
# Knowledge and Flow Policy

Definitions for the epistemic separation logic layer. A `Knowledge` binds a
string payload to a specific endpoint, representing information that a
coroutine has learned through protocol interaction. A `FlowPolicy`
decides which knowledge may propagate to which roles.

This module is deliberately small and import-cycle-free so that both `Config.lean`
(which stores the flow policy) and the `Exec*.lean` files (which read/write knowledge
sets) can depend on it.
-/

set_option autoImplicit false

/-! ## Knowledge and policies -/

structure Knowledge where
  -- Knowledge bound to a specific endpoint.
  endpoint : Endpoint
  payload : String
  deriving Repr, DecidableEq

abbrev KnowledgeSet := List Knowledge -- Snapshot of learned knowledge.

structure FlowPolicy where
  -- Decide if knowledge may flow to a role.
  allowed : Knowledge → Role → Bool
