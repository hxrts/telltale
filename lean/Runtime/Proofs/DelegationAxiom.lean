import Protocol.Coherence.EdgeCoherence
import Protocol.Environments.RoleRenaming

/-!
# Delegation Axiom (Paper 3)

The delegation preservation axiom states that receiving a delegated channel endpoint
preserves coherence (active-edge Coherent). This is the interface between Protocol-level metatheory (Paper 3)
and VM-level instruction execution.

**Development strategy:** We axiomatize delegation preservation to validate the
downstream proof structure (session-local state, frame rule, cross-session diamond).
Once the proof structure is validated, we discharge this axiom by proving Paper 3's
delegation preservation theorem (task 3.3 in implementation.md).

**The dependency chain is linear, not circular:**
```
Paper 3: Delegation preservation (single-step, Protocol level)
    ↓
R.1: VM instruction preserves SessionCoherent (uses this axiom)
    ↓
R.2: Frame rule (instructions only affect their footprint)
    ↓
R.3: Cross-session diamond (disjoint footprints commute)
```

Protocol-level proofs don't use VM theorems; VM proofs use Protocol theorems as lemmas.

## Delegation Step (from Aristotle 13b/13c)

Delegation transfers an endpoint from role A to role B in session s:
- A's endpoint is removed from GEnv
- B's endpoint is added with A's old type (with A→B renaming)
- Other participants' types have A→B renaming in session s
- Edges are redirected: (A,C)→(B,C) and (C,A)→(C,B)
- Edge traces are preserved under redirection

The key theorems (proved in Aristotle, to be ported):
- `delegateGEnv_B_lookup`: After delegation, B has A's old type
- `delegateGEnv_A_removed`: After delegation, A is removed
- `delegateDEnv_redirected_trace`: Redirected edges have original traces
- `delegate_redirected_edge_coherent`: Redirected edges are coherent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

noncomputable section

/-! ## Well-Formedness Conditions -/

/-- Well-formedness conditions for delegation from A to B in session s. -/
structure DelegationWF (G : GEnv) (s : SessionId) (A B : Role) : Prop where
  /-- A is in session s (has an endpoint) -/
  A_in_session : (lookupG G ⟨s, A⟩).isSome
  /-- B is not already in session s (simple delegation case) -/
  B_not_in_session : (lookupG G ⟨s, B⟩).isNone
  /-- A and B are distinct roles -/
  A_ne_B : A ≠ B

/-! ## Edge Redirection -/

/-- Redirect an edge from A to B in session s.
    - If sender is A, becomes B
    - If receiver is A, becomes B
    - Edges in other sessions unchanged -/
def redirectEdge (e : Edge) (s : SessionId) (A B : Role) : Edge :=
  if e.sid == s then
    { sid := s,
      sender := if e.sender == A then B else e.sender,
      receiver := if e.receiver == A then B else e.receiver }
  else e

/-- An edge e' is the redirection of edge e. -/
def IsRedirectedEdge (e e' : Edge) (s : SessionId) (A B : Role) : Prop :=
  e' = redirectEdge e s A B

/-! ## Delegation Step Relation -/

/-- A delegation step transfers an endpoint from role A to role B in session s.

    This is defined as a predicate specifying what the post-delegation environments
    must satisfy, rather than computing them explicitly.

    **GEnv conditions:**
    - A's endpoint for session s is removed
    - B's endpoint for session s is added with (a renamed version of) A's old type
    - Other endpoints are unchanged or have A→B renaming in their types

    **DEnv conditions:**
    - Edges are redirected: (A,C,s) → (B,C,s) and (C,A,s) → (C,B,s)
    - Traces are preserved under redirection
    - Edges in other sessions are unchanged

    The simple case assumes B is not already in session s. The general case
    (B already participates) requires type merging via Consume_mono (task 3.6). -/
structure DelegationStep (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) : Prop where
  /-- Well-formedness: A in session, B not in session, A ≠ B -/
  wf : DelegationWF G s A B

  /-- A's original local type in session s. -/
  A_type : LocalType

  /-- A's endpoint lookup before delegation. -/
  A_lookup : lookupG G ⟨s, A⟩ = some A_type

  /-- A is removed from session s -/
  A_removed : lookupG G' ⟨s, A⟩ = none

  /-- B gains an endpoint in session s -/
  B_added : lookupG G' ⟨s, B⟩ = some (renameLocalTypeRole s A B A_type)

  /-- Other roles in session s get their local types renamed (A → B). -/
  other_roles_G :
    ∀ ep, ep.sid = s → ep.role ≠ A → ep.role ≠ B →
      lookupG G' ep = (lookupG G ep).map (renameLocalTypeRole s A B)

  /-- Endpoints outside session s are unchanged -/
  other_sessions_G : ∀ ep, ep.sid ≠ s → lookupG G' ep = lookupG G ep

  /-- Redirected edges have the same trace as their pre-images -/
  trace_preserved : ∀ e e',
    IsRedirectedEdge e e' s A B →
    lookupD D' e' = lookupD D e

  /-- Edges in other sessions are unchanged -/
  other_sessions_D : ∀ e, e.sid ≠ s → lookupD D' e = lookupD D e

/-! ## The Axiom -/

/-- **Delegation preserves coherence (AXIOM).**

    This is the key axiom that bridges Paper 3's Protocol-level delegation preservation
    to the VM's instruction-level reasoning. It states:

    If we have coherence before a delegation step (A delegates endpoint in session s to B),
    then we have coherence after.

    **To discharge:** Prove Paper 3's delegation preservation theorem (task 3.3).
    The Aristotle files 13b/13c have proved the key supporting lemmas:
    - `delegate_redirected_edge_coherent`: Redirected edges are coherent
    - `Consume_rename_*`: Consume commutes with role renaming
    - `delegateGEnv_*`, `delegateDEnv_*`: Environment update lemmas

    The proof follows the standard three-way edge case analysis:
    1. Redirected edges (A,C)→(B,C): Use delegate_redirected_edge_coherent
    2. Edges in other sessions: Unchanged by session isolation
    3. Edges involving B on the receiver side: B now has a type, use trace_preserved

    **Tracked in:** C.1 axiom budget (implementation.md) -/
axiom delegation_preserves_coherent :
  ∀ G G' D D' s A B,
    Coherent G D →
    DelegationStep G G' D D' s A B →
    Coherent G' D'

end
