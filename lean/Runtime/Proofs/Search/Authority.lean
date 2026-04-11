import Runtime.Proofs.Search.ProfileClaims

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Authority

Generic authority-surface vocabulary for search proofs.

The search proof lane does not prove application-specific read/write region
derivation. It only needs the higher-level fact that refinement and fairness
claims are parametric in whatever downstream authority policy is chosen.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Abstract proof-side authority policy. -/
structure SearchAuthorityPolicy where
  readRegion : Nat → List Nat
  writeRegion : Nat → List Nat

/-- Abstract independence claim for two proposal targets under one authority
policy. -/
def AuthorityIndependent
    (policy : SearchAuthorityPolicy)
    (leftTarget rightTarget : Nat) : Prop :=
  ∀ ⦃node : Nat⦄, node ∈ policy.writeRegion leftTarget → node ∉ policy.writeRegion rightTarget

/-- Threaded exact single-lane refinement does not depend on how the
downstream authority policy derives regions. -/
theorem threaded_exact_single_lane_refinement_is_authority_policy_neutral
    (policy : SearchAuthorityPolicy)
    (frontier : List FrontierEntry) :
    frontierAfterThreadedExactSingleLaneStep frontier =
      frontierAfterCanonicalStep frontier := by
  simpa using threaded_exact_single_lane_step_refines_canonical frontier

/-- Canonical serial one-step fairness is likewise authority-policy neutral at
the reduced proof boundary. -/
theorem canonical_serial_fairness_is_authority_policy_neutral
    (policy : SearchAuthorityPolicy)
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterCanonicalStep frontier := by
  exact canonical_serial_goal_window_service_has_exact_suffix_bound hMin

end Search
end Proofs
end Runtime
