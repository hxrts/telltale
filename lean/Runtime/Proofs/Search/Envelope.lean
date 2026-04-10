import Runtime.Proofs.Search.ProfileClaims

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Envelope

Certified-window theorem surface for the envelope-bounded batched profile.

The strengthened proof lane no longer treats
`batchedParallelEnvelopeBounded` as a documentation-only design boundary. It
now exposes an explicit certified-window object and premise-scoped fairness
theorems, parallel to the existing batched-exact lane.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Certified service object for one envelope-bounded legal window. -/
structure BatchedEnvelopeWindowCertificate (frontier : List FrontierEntry) where
  servicedEntries : List FrontierEntry
  normalizedCommits : List NormalizedCommit
  envelopeWidth : Nat
  normalizationMode : String
  serviceBoundSteps : Nat
  coversCurrentMinKeyBatch :
    ∀ ⦃entry : FrontierEntry⦄,
      entry ∈ canonicalBatch frontier →
      entry ∈ servicedEntries
  commitTraceCoversCurrentMinKeyBatch :
    ∀ ⦃entry : FrontierEntry⦄,
      entry ∈ canonicalBatch frontier →
      ∃ commit, commit ∈ normalizedCommits ∧ commit.node = entry.node

/-- Post-window frontier under one certified envelope-bounded service window. -/
def frontierAfterEnvelopeBatchWindow
    (frontier : List FrontierEntry)
    (certificate : BatchedEnvelopeWindowCertificate frontier) : List FrontierEntry :=
  frontier.filter (fun entry => entry ∉ certificate.servicedEntries)

/-- Exported certified-window trace entry for one envelope profile window. -/
def certifiedEnvelopeWindowTraceEntryOfCertificate
    (frontier : List FrontierEntry)
    (certificate : BatchedEnvelopeWindowCertificate frontier) : CertifiedWindowTraceEntry :=
  { epoch := 0
  , phase := 0
  , normalizationMode := certificate.normalizationMode
  , serviceBoundSteps := certificate.serviceBoundSteps
  , batchNodes := certificate.servicedEntries.map FrontierEntry.node
  , normalizedCommits := certificate.normalizedCommits
  }

/-- A certified envelope window covers the current legal min-key batch. -/
theorem certified_batched_envelope_window_is_fair
    {frontier : List FrontierEntry}
    (certificate : BatchedEnvelopeWindowCertificate frontier)
    {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterEnvelopeBatchWindow frontier certificate := by
  intro hAfter
  simp [frontierAfterEnvelopeBatchWindow] at hAfter
  have hBatch : entry ∈ canonicalBatch frontier :=
    min_priority_entry_serviced_next_step hMin
  exact hAfter.2 (certificate.coversCurrentMinKeyBatch hBatch)

/-- The envelope profile now advertises the same theorem-backed claim class as
other certified-window profiles. -/
theorem batched_parallel_envelope_claim_is_certified_window_bounded :
    fairnessClaimClass .batchedParallelEnvelopeBounded = .premisedWindowBounded :=
  batched_parallel_envelope_claim_is_premised

/-- One certified envelope window therefore yields one-window eventual service
for currently legal min-priority entries. -/
theorem certified_batched_envelope_window_eventually_services_min_priority_entries
    {trace : FrontierTrace} {start : Nat}
    (certificate : BatchedEnvelopeWindowCertificate (trace start))
    (hStep : trace (start + 1) =
      frontierAfterEnvelopeBatchWindow (trace start) certificate)
    {entry : FrontierEntry}
    (hMin : IsMinPriority (trace start) entry) :
    EventuallyServicedWithin trace start 1 entry := by
  refine ⟨0, Nat.zero_lt_one, ?_⟩
  simpa [EventuallyServicedWithin, hStep] using
    certified_batched_envelope_window_is_fair certificate hMin

/-- Certified envelope-window traces are structurally valid when each exported
certificate services the legal current min-key batch and publishes the standard
one-window bound. -/
theorem certified_envelope_window_trace_is_valid
    {trace : FrontierTrace} {start bound : Nat}
    (certificates : ∀ j : Fin bound, BatchedEnvelopeWindowCertificate (trace (start + j.1)))
    (hBatchExact : ∀ j : Fin bound,
      (certificates j).servicedEntries = canonicalBatch (trace (start + j.1)))
    (hBound : ∀ j : Fin bound, (certificates j).serviceBoundSteps = 1) :
    CertifiedWindowTraceValid trace start bound
      (fun j => certifiedEnvelopeWindowTraceEntryOfCertificate (trace (start + j.1)) (certificates j)) := by
  intro j
  constructor
  · simpa using hBound j
  · simp [certifiedEnvelopeWindowTraceEntryOfCertificate, hBatchExact j]

end Search
end Proofs
end Runtime
