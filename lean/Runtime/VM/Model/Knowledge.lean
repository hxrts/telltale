import Runtime.VM.Model.Core

/-! # Runtime.VM.Model.Knowledge

Definitions for the epistemic separation logic layer. A `Knowledge` binds a
string payload to a specific endpoint, representing information that a
coroutine has learned through protocol interaction. A `FlowPolicy`
decides which knowledge may propagate to which roles.

This module is deliberately small and import-cycle-free so that both `Config.lean`
(which stores the flow policy) and the `Exec*.lean` files (which read/write knowledge
sets) can depend on it.
-/

/-
The Problem. The VM model needs a small, serializable vocabulary for knowledge
facts and flow policies that can be used uniformly by state, semantics, and
runtime conformance checks.

Solution Structure. Define endpoint-bound knowledge atoms, predicate/policy
interpreters, and serialization round-trips in one import-light module.
-/

set_option autoImplicit false

/-! ## Knowledge and policies -/

structure Knowledge where
  -- Knowledge bound to a specific endpoint.
  endpoint : Endpoint
  payload : String
  deriving Repr, DecidableEq

abbrev KnowledgeSet := List Knowledge -- Snapshot of learned knowledge.

inductive FlowPredicate where
  -- Allow when destination role starts with a prefix.
  | targetRolePrefix (pfx : String)
  -- Allow when fact payload contains a fragment.
  | factContains (fragment : String)
  -- Allow when endpoint role matches the destination role.
  | endpointRoleMatchesTarget
  -- Conjunction.
  | all (predicates : List FlowPredicate)
  -- Disjunction.
  | any (predicates : List FlowPredicate)
  deriving Repr

/-! ### Flow Predicate Evaluation -/

private def stringContains (text fragment : String) : Bool :=
  if fragment.isEmpty then
    true
  else
    -- `splitOn` yields >1 chunks iff the separator appears.
    (text.splitOn fragment).length > 1

mutual
  private def predicateDepth : FlowPredicate → Nat
    | .targetRolePrefix _ => 1
    | .factContains _ => 1
    | .endpointRoleMatchesTarget => 1
    | .all preds => listDepth preds + 1
    | .any preds => listDepth preds + 1

  private def listDepth : List FlowPredicate → Nat
    | [] => 0
    | p :: ps => Nat.max (predicateDepth p) (listDepth ps)
end

private def evalFuel (fuel : Nat) (pred : FlowPredicate) (knowledge : Knowledge) (targetRole : Role) : Bool :=
  match fuel with
  | 0 => false
  | n + 1 =>
      match pred with
      | .targetRolePrefix pfx => targetRole.startsWith pfx
      | .factContains fragment => stringContains knowledge.payload fragment
      | .endpointRoleMatchesTarget => decide (knowledge.endpoint.role = targetRole)
      | .all preds => preds.all (fun p => evalFuel n p knowledge targetRole)
      | .any preds => preds.any (fun p => evalFuel n p knowledge targetRole)

def FlowPredicate.eval (pred : FlowPredicate) (knowledge : Knowledge) (targetRole : Role) : Bool :=
  evalFuel (predicateDepth pred + 1) pred knowledge targetRole

/-! ### Runtime Flow Policies -/

inductive FlowPolicy where
  -- Permit all facts to all roles.
  | allowAll
  -- Deny all flows.
  | denyAll
  -- Permit only listed roles.
  | allowRoles (roles : List Role)
  -- Deny listed roles.
  | denyRoles (roles : List Role)
  -- Runtime closure policy (non-serializable): PARITY_BREAK requires explicit justification.
  | predicate (allowed : Knowledge → Role → Bool)
  -- Serializable predicate expression.
  | predicateExpr (pred : FlowPredicate)

def FlowPolicy.allows (policy : FlowPolicy) (targetRole : Role) : Bool :=
  match policy with
  | .allowAll => true
  | .denyAll => false
  | .allowRoles roles => roles.contains targetRole
  | .denyRoles roles => !(roles.contains targetRole)
  | .predicate _ | .predicateExpr _ => true

def FlowPolicy.allowsKnowledge (policy : FlowPolicy) (knowledge : Knowledge) (targetRole : Role) : Bool :=
  match policy with
  | .predicate allowed => allowed knowledge targetRole
  | .predicateExpr pred => pred.eval knowledge targetRole
  | other => other.allows targetRole

/-! ### Serializable Policy Representations -/

inductive FlowPolicyRepr where
  -- Permit all facts to all roles.
  | allowAll
  -- Deny all flows.
  | denyAll
  -- Permit only listed roles.
  | allowRoles (roles : List Role)
  -- Deny listed roles.
  | denyRoles (roles : List Role)
  -- Serializable predicate expression.
  | predicateExpr (pred : FlowPredicate)
  deriving Repr

def FlowPolicy.toRepr? (policy : FlowPolicy) : Option FlowPolicyRepr :=
  match policy with
  | .allowAll => some .allowAll
  | .denyAll => some .denyAll
  | .allowRoles roles => some (.allowRoles roles)
  | .denyRoles roles => some (.denyRoles roles)
  | .predicate _ => none
  | .predicateExpr pred => some (.predicateExpr pred)

def FlowPolicy.ofRepr (repr : FlowPolicyRepr) : FlowPolicy :=
  match repr with
  | .allowAll => .allowAll
  | .denyAll => .denyAll
  | .allowRoles roles => .allowRoles roles
  | .denyRoles roles => .denyRoles roles
  | .predicateExpr pred => .predicateExpr pred

/-! Proof-only roundtrip laws are in `Runtime.Proofs.VM.Knowledge`. -/
