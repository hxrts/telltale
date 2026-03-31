set_option autoImplicit false

/-! # Runtime.Proofs.Capabilities

Canonical taxonomy and module boundary for Telltale's first-class
protocol-critical capability model.

This module does not introduce a new executable mechanism by itself.
Its job is to make the design boundary explicit in the Lean proof tree so Rust
and docs can point at one theorem/model surface rather than several ad hoc
ones.
-/

namespace Runtime
namespace Proofs

/-- Canonical protocol-critical capability classes. -/
inductive ProtocolCriticalCapabilityClass where
  | admission
  | ownership
  | evidence
  | transition
  deriving DecidableEq, Repr

/-- Shared lifecycle vocabulary for first-class capability and evidence objects. -/
inductive ProtocolCriticalCapabilityLifecycleState where
  | issued
  | consumed
  | rejected
  | invalidated
  | committed
  | rolledBack
  | expired
  deriving DecidableEq, Repr

/-- Source-derived theorem/model boundary row for one capability surface. -/
structure ProtocolCriticalCapabilityBoundaryEntry where
  surface : String
  capabilityClass : ProtocolCriticalCapabilityClass
  lifecycle : List ProtocolCriticalCapabilityLifecycleState
  rustModule : String
  leanModule : String
  rationale : String
  deriving DecidableEq, Repr

/-- Canonical theorem/model boundary for the first-class capability model. -/
def protocolCriticalCapabilityBoundary :
    List ProtocolCriticalCapabilityBoundaryEntry :=
  [ { surface := "runtime_admission"
    , capabilityClass := .admission
    , lifecycle := [.issued, .rejected]
    , rustModule := "rust/machine/src/runtime_contracts.rs"
    , leanModule := "lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean"
    , rationale := "Admits or rejects runtime/profile execution before protocol-critical execution begins."
    }
  , { surface := "theorem_pack_capabilities"
    , capabilityClass := .admission
    , lifecycle := [.issued, .rejected]
    , rustModule := "rust/machine/src/composition.rs"
    , leanModule := "lean/Runtime/Proofs/TheoremPack/API.lean"
    , rationale := "Carries proof-backed eligibility that higher-level runtime admission consumes."
    }
  , { surface := "ownership_capability"
    , capabilityClass := .ownership
    , lifecycle := [.issued, .invalidated, .expired, .rejected]
    , rustModule := "rust/machine/src/session/overview.rs"
    , leanModule := "lean/Runtime/Proofs/Conservation/Authority.lean"
    , rationale := "Proves which actor may currently mutate session-local protocol-critical state."
    }
  , { surface := "readiness_witness"
    , capabilityClass := .evidence
    , lifecycle := [.issued, .consumed, .rejected, .invalidated, .expired]
    , rustModule := "rust/machine/src/session/overview.rs"
    , leanModule := "lean/Runtime/Proofs/AuthorityMetatheory.lean"
    , rationale := "Justifies a protocol-critical readiness decision under one live owner generation."
    }
  , { surface := "authoritative_read"
    , capabilityClass := .evidence
    , lifecycle := [.issued, .consumed, .rejected]
    , rustModule := "rust/machine/src/semantic_objects.rs"
    , leanModule := "lean/Runtime/Proofs/Conservation/Evidence.lean"
    , rationale := "Carries evidence-bearing protocol input that may author canonical truth."
    }
  , { surface := "materialization_proof"
    , capabilityClass := .evidence
    , lifecycle := [.issued, .consumed, .rejected]
    , rustModule := "rust/machine/src/semantic_objects.rs"
    , leanModule := "lean/Runtime/Proofs/Conservation/Evidence.lean"
    , rationale := "Witnesses proof-bearing success on the sanctioned materialization path."
    }
  , { surface := "canonical_handle"
    , capabilityClass := .evidence
    , lifecycle := [.issued, .consumed, .rejected, .invalidated]
    , rustModule := "rust/machine/src/semantic_objects.rs"
    , leanModule := "lean/Runtime/Proofs/Conservation/Evidence.lean"
    , rationale := "Provides the strong reference required on parity-critical follow-on paths."
    }
  , { surface := "ownership_receipt"
    , capabilityClass := .transition
    , lifecycle := [.issued, .committed, .rolledBack, .rejected, .invalidated, .expired]
    , rustModule := "rust/machine/src/session/overview.rs"
    , leanModule := "lean/Runtime/Proofs/Conservation/Authority.lean"
    , rationale := "Stages and commits explicit ownership transfer rather than ambient authority mutation."
    }
  , { surface := "semantic_handoff"
    , capabilityClass := .transition
    , lifecycle := [.committed, .rolledBack, .rejected, .invalidated]
    , rustModule := "rust/machine/src/semantic_objects.rs"
    , leanModule := "lean/Runtime/Proofs/Conservation/Authority.lean"
    , rationale := "Represents explicit protocol-visible authority transfer and old-owner revocation."
    }
  , { surface := "reconfiguration_transition"
    , capabilityClass := .transition
    , lifecycle := [.issued, .committed, .rolledBack, .rejected]
    , rustModule := "rust/machine/src/composition.rs"
    , leanModule := "lean/Runtime/Proofs/ReconfigurationObserver.lean"
    , rationale := "Captures protocol-critical cutover and membership/runtime transition artifacts."
    }
  ]

/-- Canonical Lean theorem/model module boundary for the first-class capability model. -/
def firstClassCapabilityLeanModuleBoundary : List String :=
  [ "lean/Runtime/Proofs/Capabilities.lean"
  , "lean/Runtime/Proofs/AuthorityMetatheory.lean"
  , "lean/Runtime/Proofs/Conservation/Authority.lean"
  , "lean/Runtime/Proofs/Conservation/Evidence.lean"
  , "lean/Runtime/Proofs/ReconfigurationObserver.lean"
  , "lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean"
  ]

theorem protocolCriticalCapabilityBoundary_nonempty :
    protocolCriticalCapabilityBoundary ≠ [] := by
  native_decide

theorem capabilityBoundary_covers_all_classes :
    (∃ entry ∈ protocolCriticalCapabilityBoundary, entry.capabilityClass = .admission) ∧
    (∃ entry ∈ protocolCriticalCapabilityBoundary, entry.capabilityClass = .ownership) ∧
    (∃ entry ∈ protocolCriticalCapabilityBoundary, entry.capabilityClass = .evidence) ∧
    (∃ entry ∈ protocolCriticalCapabilityBoundary, entry.capabilityClass = .transition) := by
  native_decide

end Proofs
end Runtime
