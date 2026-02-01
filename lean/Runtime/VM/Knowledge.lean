import Runtime.VM.Core

/-!
# Knowledge Facts and Flow Policy

Definitions for the epistemic separation logic layer (`runtime.md` §16). A
`KnowledgeFact` binds a string payload to a specific endpoint, representing
information that a coroutine has learned through protocol interaction. A
`FlowPolicy` decides which facts may propagate to which roles.

This module is deliberately small and import-cycle-free so that both `Config.lean`
(which stores the flow policy) and the `Exec*.lean` files (which read/write knowledge
sets) can depend on it.
-/

set_option autoImplicit false

/-! ## Knowledge facts and policies -/

structure KnowledgeFact where
  -- Knowledge fact bound to a specific endpoint.
  endpoint : Endpoint
  fact : String
  deriving Repr, DecidableEq

abbrev KnowledgeSet := List KnowledgeFact -- Snapshot of learned facts.

structure FlowPolicy where
  -- Decide if a knowledge fact may flow to a role.
  allowed : KnowledgeFact → Role → Bool
