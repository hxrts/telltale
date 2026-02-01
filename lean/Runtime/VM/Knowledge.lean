import Runtime.VM.Core

/-
The Problem. The VM needs a shared definition of knowledge facts and
flow policies that can be referenced by both config and execution
without creating import cycles.

Solution Structure. Define endpoint-bound knowledge facts, knowledge
sets, and a simple flow policy predicate in a dedicated module.
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
