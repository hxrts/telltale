import Protocol.Coherence.EdgeCoherence

/-!
# Delegation Axiom (Paper 3)

The delegation preservation axiom states that receiving a delegated channel endpoint
preserves coherence. This is the interface between Protocol-level metatheory (Paper 3)
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
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

noncomputable section

/-- Placeholder for delegation step relation.
    In Paper 3, this will be defined as: role A delegates endpoint for session s to role B.
    The message payload contains `chan s L` where L is the delegated local type. -/
def DelegationStep (G G' : GEnv) (D D' : DEnv) (_s : SessionId) (_A _B : Role) : Prop :=
  -- Placeholder: will be replaced by actual definition in Paper 3
  -- A delegation step transfers an endpoint from A to B:
  -- - A's type for s changes (endpoint sent away)
  -- - B's type for s changes (endpoint received)
  -- - Buffer on (A → B) changes (message containing endpoint consumed)
  -- - All other edges unchanged
  True ∧ G' = G' ∧ D' = D' -- Use params to avoid unused variable warnings

/-- **Delegation preserves coherence (AXIOM).**

    This is the key axiom that bridges Paper 3's Protocol-level delegation preservation
    to the VM's instruction-level reasoning. It states:

    If we have coherence before a delegation step (A delegates endpoint in session s to B),
    then we have coherence after.

    **To discharge:** Prove Paper 3's delegation preservation theorem (task 3.3).
    The proof will show that delegation is a special case of message passing where
    the payload type is `chan s L`, and coherence preservation follows from the
    higher-order coherence definitions (tasks 3.1, 3.2).

    **Tracked in:** C.1 axiom budget (implementation.md) -/
axiom delegation_preserves_coherent :
  ∀ G G' D D' s A B,
    Coherent G D →
    DelegationStep G G' D D' s A B →
    Coherent G' D'

end
