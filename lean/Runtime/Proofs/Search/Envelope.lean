import Runtime.Proofs.Search.ProfileClaims

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Envelope

Explicit design boundary for the envelope-bounded batched profile.

The current runtime surface intentionally keeps
`batchedParallelEnvelopeBounded` out of the theorem-backed fairness lane unless
an additional frontier-window certificate and refinement story are supplied.
This module makes that non-theorem boundary first-class so the profile is no
longer "missing a proof by accident".
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Why the current proof lane does not claim unconditional fairness for the
envelope-bounded profile. -/
inductive EnvelopeFairnessGapReason where
  | noCertifiedFrontierWindow
  | noCanonicalCommitRefinement
  | noObservationEquivalenceTheorem
  deriving DecidableEq, Repr

/-- Checked-in design review for the envelope-bounded profile. -/
structure EnvelopeFairnessDesignBoundary where
  reasons : List EnvelopeFairnessGapReason
  keepsClaimClassPremiseOnly :
    fairnessClaimClass .batchedParallelEnvelopeBounded = .premiseOnly
  deriving Repr

/-- The envelope-bounded profile remains premise-only by explicit design review,
not by omission. -/
theorem batched_parallel_envelope_design_boundary_is_explicit :
    ∃ boundary : EnvelopeFairnessDesignBoundary,
      boundary.reasons =
        [ EnvelopeFairnessGapReason.noCertifiedFrontierWindow
        , EnvelopeFairnessGapReason.noCanonicalCommitRefinement
        , EnvelopeFairnessGapReason.noObservationEquivalenceTheorem
        ] := by
  let boundary : EnvelopeFairnessDesignBoundary :=
    { reasons :=
        [ EnvelopeFairnessGapReason.noCertifiedFrontierWindow
        , EnvelopeFairnessGapReason.noCanonicalCommitRefinement
        , EnvelopeFairnessGapReason.noObservationEquivalenceTheorem
        ]
    , keepsClaimClassPremiseOnly := batched_parallel_envelope_claim_is_premise_only
    }
  refine ⟨boundary, rfl⟩

end Search
end Proofs
end Runtime
