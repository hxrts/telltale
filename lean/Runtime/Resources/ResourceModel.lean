import Runtime.VM.TypeClasses
import Runtime.Compat.RA

/-
The Problem. The runtime needs a lightweight resource model for V1 that
tracks committed resources and nullifiers without committing to SMT or ZK.

Solution Structure. Define core resource/transaction structures and an
accumulated-set interface, leaving proofs and advanced data structures
for later profiles.
-/

set_option autoImplicit false

universe u

/-! ## Resource core types -/

abbrev ResourceLogicRef (ν : Type u) [VerificationModel ν] :=
  -- Hash of the governing predicate.
  VerificationModel.Hash ν

abbrev LabelRef (ν : Type u) [VerificationModel ν] :=
  -- Hash of the fungibility domain.
  VerificationModel.Hash ν

abbrev ValueRef :=
  -- Placeholder for resource payloads.
  Value

abbrev Delta :=
  -- Placeholder for delta accounting.
  Int

/-- Resource records are immutable and committed. -/
structure Resource (ν : Type u) [VerificationModel ν] where
  logic : ResourceLogicRef ν -- Governing predicate reference.
  label : LabelRef ν -- Fungibility label.
  quantity : Nat -- Quantity within the kind.
  value : ValueRef -- Payload value (opaque in V1).
  nonce : VerificationModel.Nonce ν -- Uniqueness seed.
  ckey : VerificationModel.CommitmentKey ν -- Commitment key for the resource.
  nullifierKey : VerificationModel.NullifierKey ν -- Nullifier key for spending.
  isEphemeral : Bool -- Whether the resource persists across transactions.

/-- Serialize a resource for hashing/commitment (placeholder). -/
def resourcePayload {ν : Type u} [VerificationModel ν] (_r : Resource ν) : Data :=
  -- Replace with a real encoding when Value serialization is fixed.
  Value.unit

/-- Commitment for a resource. -/
def Resource.commitment {ν : Type u} [VerificationModel ν]
    (r : Resource ν) : VerificationModel.Commitment ν :=
  -- Commit to the resource payload under the commitment key.
  VerificationModel.commit r.ckey (resourcePayload r) r.nonce

/-- Nullifier for a resource. -/
def Resource.nullifier {ν : Type u} [VerificationModel ν]
    (r : Resource ν) : VerificationModel.Nullifier ν :=
  -- Nullify the resource payload with the nullifier key.
  VerificationModel.nullify (resourcePayload r) r.nullifierKey

/-- Resource kind derived from logic + label. -/
def Resource.kind {ν : Type u} [VerificationModel ν]
    (r : Resource ν) : VerificationModel.Hash ν :=
  -- Domain-separated hash for the resource kind.
  VerificationModel.hashTagged .resourceKind (resourcePayload r)

/-- Resource delta contribution (placeholder). -/
def Resource.delta {ν : Type u} [VerificationModel ν]
    (_r : Resource ν) : Delta :=
  -- V1 uses a stubbed delta accounting.
  0

/-- Map a commitment payload into an accumulated-set key. -/
def commitmentKey {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (r : Resource ν) : AccumulatedSet.Key ν :=
  -- V1 hashes the payload to derive a key.
  AccumulatedSet.keyOfHash (VerificationModel.hashTagged .commitment (resourcePayload r))

/-- Map a nullifier payload into an accumulated-set key. -/
def nullifierKey {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (r : Resource ν) : AccumulatedSet.Key ν :=
  -- V1 hashes the payload to derive a key.
  AccumulatedSet.keyOfHash (VerificationModel.hashTagged .nullifier (resourcePayload r))

/-! ## Resource state and transactions -/

/-- Local state for committed resources (scoped). -/
structure ResourceState (ν : Type u) [VerificationModel ν] [AccumulatedSet ν] where
  scope : ScopeId -- Local view identifier.
  commitments : AccumulatedSet.State ν -- Committed resources in scope.
  nullifiers : AccumulatedSet.State ν -- Spent-resource set in scope.

abbrev ResourceLogicProof :=
  -- Placeholder for logic proof objects.
  Unit

abbrev ComplianceProof (ν : Type u) [VerificationModel ν] [AccumulatedSet ν] :=
  -- Pair of membership and non-membership proofs.
  AccumulatedSet.ProofMember ν × AccumulatedSet.ProofNonMember ν

abbrev DeltaProof :=
  -- Placeholder for balance proofs.
  Unit

/-- Transaction bundles resource creation and consumption. -/
structure Transaction (ν : Type u) [VerificationModel ν] [AccumulatedSet ν] where
  created : List (Resource ν) -- Newly created resources.
  consumed : List (Resource ν) -- Resources consumed in this step.
  deltaProof : DeltaProof -- Balance proof (stub in V1).
  logicProofs : List ResourceLogicProof -- Predicate proofs (stub in V1).
  complianceProofs : List (ComplianceProof ν) -- Membership/non-membership proofs.
  authorizedImbalance : Bool -- Whether a non-zero delta is authorized.

/-- Delta balance predicate for a transaction (stub). -/
def txBalanced {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (_tx : Transaction ν) : Prop :=
  -- V1 leaves balance checking abstract.
  True

/-- Transaction validity for a given resource state (V1). -/
def Transaction.valid {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (tx : Transaction ν) (st : ResourceState ν) : Prop :=
  -- Membership and non-membership are delegated to the accumulated-set interface.
  txBalanced tx ∧
  (tx.authorizedImbalance ∨ txBalanced tx) ∧
  (∀ r ∈ tx.consumed, ∃ p ∈ tx.complianceProofs,
    AccumulatedSet.verifyMember st.commitments (commitmentKey r) p.1 = true ∧
    AccumulatedSet.verifyNonMember st.nullifiers (nullifierKey r) p.2 = true) ∧
  (∀ r ∈ tx.created, ∃ p ∈ tx.complianceProofs,
    AccumulatedSet.verifyNonMember st.commitments (commitmentKey r) p.2 = true)
