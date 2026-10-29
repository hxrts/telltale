import Runtime.Proofs.TheoremPack.InventoryJson
import Runtime.ProtocolMachine.Model.UnitModel

/-! # Concrete Envelope Evidence Pack

A concrete theorem pack over `UnitVerify` with an empty session store and
`Unit` state, used by the `theorem_evidence_export` executable to emit the
evidence inventory consumed by Rust admission.

Envelope profiles attached here are built from genuine proofs for the
degenerate instance in which every state, observation, placement, protocol,
and deployment is `Unit`. On `Unit`, all erased runs coincide, so every
envelope equivalence holds by `funext`; no `sorry` or axiom is used. This is
evidence for the trivial instance only, not for any non-trivial protocol.

The envelope-admission profile is *not* attached: its premise bundle is
uninhabited for every `State`/`Obs` (`admissionPremises_uninhabited`), because
the diagnostics soundness and completeness fields quantify over all `DUser`
with a `failedObligation` predicate that cannot depend on the user. -/

set_option autoImplicit false

namespace Runtime
namespace Proofs
namespace Examples

open Runtime.Adequacy

/-! ## Unit Envelope Witnesses -/

/-- Every local envelope over `Unit` relates all runs. -/
theorem unit_eqEnvLocal (E : LocalEnvelope Unit Unit) (r₁ r₂ : Run Unit) :
    EqEnvLocal E r₁ r₂ :=
  funext fun _ => rfl

/-- Every sharded envelope over `Unit` relates all runs. -/
theorem unit_eqEnvShard (E : ShardedEnvelope Unit Unit) (r₁ r₂ : Run Unit) :
    EqEnvShard E r₁ r₂ :=
  funext fun _ => rfl

/-- Trivial envelope relation over `Unit`. -/
def unitEnvelope : EnvelopeRelation Unit Unit :=
  { observe := fun _ => (), rel := fun _ _ => True }

/-- Local hypothesis bundle over `Unit`, discharged by `unit_eqEnvLocal`. -/
def unitLocalHypotheses : ProtocolMachineLocalEnvelopeHypotheses Unit Unit :=
  { localEnvelope := ⟨unitEnvelope⟩
  , refRun := fun _ => True
  , vmRun := fun _ => True
  , certifiedExchange := fun _ _ => True
  , adherenceWitness := fun r i _ _ => unit_eqEnvLocal _ r i
  , schedulerDeterminismWitness := fun _ r₂ _ i₂ _ _ _ => unit_eqEnvLocal _ r₂ i₂ }

/-- Sharded hypothesis bundle over `Unit`, discharged by `unit_eqEnvShard`. -/
def unitShardedHypotheses : ProtocolMachineShardedEnvelopeHypotheses Unit Unit :=
  { shardedEnvelope := ⟨unitEnvelope⟩
  , refRun := fun _ => True
  , vmRun := fun _ => True
  , certifiedExchange := fun _ _ => True
  , adherenceWitness := fun r i _ _ => unit_eqEnvShard _ r i
  , schedulerDeterminismWitness := fun _ r₂ _ i₂ _ _ _ => unit_eqEnvShard _ r₂ i₂ }

/-- Capability strength is reflexive. -/
theorem capabilityStrengthens_refl (c : CertifiedEnvelopeCapability) :
    CapabilityStrengthens c c :=
  ⟨Nat.le_refl _, id, fun _ h => h⟩

/-! ## Envelope Adherence Profile -/

/-- Adherence premises over `Unit`. The `assumed*` fields hold outright:
the obligation and guarantee are constantly `True`. -/
def unitAdherencePremises : ProtocolMachineEnvelopeAdherencePremises Unit Unit Unit :=
  { localHypotheses := unitLocalHypotheses
  , shardedHypotheses := unitShardedHypotheses
  , subtype := fun _ _ => True
  , obligation := fun _ _ _ => True
  , assumedSpatialMonotonicity := fun _ _ _ _ _ h => h
  , guarantee := fun _ => True
  , weakCapability := default
  , strongCapability := default
  , assumedCapabilityMonotonicity := fun _ _ _ h => h
  , strongStrengthensWeak := capabilityStrengthens_refl _ }

/-- Concrete envelope-adherence profile (all derived fields use defaults). -/
def unitAdherenceProfile : Adapters.ProtocolMachineEnvelopeAdherenceProfile :=
  { State := Unit, Obs := Unit, Placement := Unit, premises := unitAdherencePremises }

/-! ## Envelope Bridge Profile -/

/-- Bridge premises over `Unit`: identity semantics, zero bounds, and
`True` obligations, with every `assumed*` field proved. -/
def unitBridgePremises : ProtocolEnvelopeBridgePremises Unit Unit Unit Unit Unit :=
  { localEnvelope := ⟨unitEnvelope⟩
  , shardedEnvelope := ⟨unitEnvelope⟩
  , roleRenaming := { renameRun := fun _ r => r }
  , composition := { composeRun := fun _ _ r => r }
  , delegation := { delegateRun := fun _ r => r }
  , spatial := { subtype := fun _ _ _ => True }
  , exchange := { exchange := fun _ _ _ => True }
  , shardCut := { cut := fun _ _ _ => True, runOf := fun _ _ => () }
  , component₁ := fun _ _ => 0
  , component₂ := fun _ _ => 0
  , interaction := fun _ _ => 0
  , total := fun _ _ => 0
  , obligation := fun _ _ _ => True
  , assumedRoleRenamingInvariant := fun _ r i _ => unit_eqEnvLocal _ r i
  , assumedCompositionalEnvelope := fun _ _ _ _ => rfl
  , assumedDelegationPreserves := fun _ r i _ => unit_eqEnvLocal _ r i
  , assumedSpatialMonotonicity := fun _ _ _ _ _ _ h => h
  , assumedExchangeNormalization := fun _ _ r₂ _ i₂ _ _ _ => unit_eqEnvLocal _ r₂ i₂
  , assumedShardCutPreservation := fun _ d₁ d₂ _ => unit_eqEnvShard _ _ _ }

/-- Concrete envelope-bridge profile. -/
def unitBridgeProfile : Adapters.ProtocolEnvelopeBridgeProfile :=
  { Protocol := Unit, Placement := Unit, Deployment := Unit, State := Unit, Obs := Unit
  , bundle := { premises := unitBridgePremises } }

/-! ## Envelope Admission Obstruction -/

/-- The envelope-admission premise bundle has no inhabitant: a user with
`maxRequestedDiff` beyond the local capability forces
`failedObligation .withinMaxDiff` (diagnostics soundness), while the
permissive user has no rejection reasons, so completeness refutes it. -/
theorem admissionPremises_uninhabited {State : Type} {Obs : Type}
    (p : ProtocolMachineEnvelopeAdmissionPremises State Obs) : False := by
  let overUser : DUser :=
    { maxRequestedDiff := (DProg_local p.input).maxDiff + 1
    , eqSafeOnly := false, requiredProfiles := [] }
  let permissive : DUser :=
    { maxRequestedDiff := 0, eqSafeOnly := false, requiredProfiles := [] }
  have hFailed : p.failedObligation .withinMaxDiff :=
    p.diagnosticsSoundnessLocal overUser .maxDiffExceeded
      (by simp [admissionRejectionReasons, overUser])
  obtain ⟨r, hr, _⟩ := p.diagnosticsCompletenessLocal permissive _ hFailed
  simp [admissionRejectionReasons, permissive] at hr

/-! ## Concrete Pack and Inventory -/

/-- Empty session store over the unit verification model. -/
def unitStore : SessionStore UnitVerify := []

/-- Invariant space with only the provable envelope profiles attached. -/
noncomputable def envelopeEvidenceSpace : ProtocolMachineInvariantSpaceWithProfiles unitStore Unit :=
  (ProtocolMachineInvariantSpaceWithProfiles.mk
    (Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles.mk
      (ProtocolMachineInvariantSpace.mk none none none none) {}) {}
  ).withProtocolMachineEnvelopeAdherence unitAdherenceProfile
   |>.withProtocolEnvelopeBridge unitBridgeProfile

/-- Theorem pack built from `envelopeEvidenceSpace`. -/
noncomputable def envelopeEvidencePack : ProtocolMachineTheoremPack (space := envelopeEvidenceSpace) :=
  buildProtocolMachineTheoremPack (space := envelopeEvidenceSpace)

/-- Evaluated inventory of `envelopeEvidencePack`. The pack is noncomputable
(its default classical profiles depend on real analysis), so the exported list
is a literal that `envelopeEvidenceInventory_eq` proves equal to
`theoremInventory envelopeEvidencePack` by kernel reduction. -/
def envelopeEvidenceInventory : List (String × Bool) :=
  [ ("termination", false)
  , ("output_condition_soundness", false)
  , ("flp_lower_bound", false)
  , ("flp_impossibility", false)
  , ("cap_impossibility", false)
  , ("quorum_geometry_safety", false)
  , ("partial_synchrony_liveness", false)
  , ("responsiveness", false)
  , ("nakamoto_security", false)
  , ("reconfiguration_safety", false)
  , ("atomic_broadcast_ordering", false)
  , ("accountable_safety", false)
  , ("failure_detector_boundaries", false)
  , ("data_availability_retrievability", false)
  , ("coordination_characterization", false)
  , ("calm_characterization", false)
  , ("crdt_envelope_and_equivalence", false)
  , ("crdt_monotonicity", false)
  , ("triangle_of_forgetting_impossibility", false)
  , ("byzantine_safety_characterization", false)
  , ("consensus_envelope", false)
  , ("failure_envelope", false)
  , ("protocol_machine_envelope_adherence", true)
  , ("protocol_machine_envelope_admission", false)
  , ("protocol_envelope_bridge", true)
  , ("effect_interface_bridge", true)
  , ("classical_foster", false)
  , ("classical_maxweight", false)
  , ("classical_ldp", false)
  , ("classical_mean_field", false)
  , ("classical_heavy_traffic", false)
  , ("classical_mixing", false)
  , ("classical_fluid", false)
  , ("classical_concentration", false)
  , ("classical_littles_law", false)
  , ("classical_functional_clt", false)
  , ("classical_spectral_gap_termination", false)
  , ("semantic_object_core_invariants", false)
  , ("semantic_object_outstanding_effects", false)
  , ("semantic_object_semantic_handoffs", false)
  , ("semantic_object_authoritative_reads_publication", false)
  , ("semantic_object_materialization_success", false)
  , ("semantic_object_progress_contracts", false)
  , ("semantic_object_effect_contracts", false)
  , ("semantic_object_replay_failure_exactness", false)
  , ("semantic_object_cross_target_progress_dependent_work", false)
  , ("semantic_object_transformation_local_obligations", false)
  , ("profile_fairness_schedule_confluence", true)
  , ("profile_fairness_starvation_freedom", true)
  , ("profile_progress_contract_bounded", true)
  , ("profile_protocol_bridge_bounded", true)
  , ("metadata_progress_contracts_premise_supplied", false)
  , ("metadata_replay_failure_exactness_premise_supplied", false)
  , ("metadata_envelope_adherence_premise_supplied", true)
  , ("metadata_envelope_admission_premise_supplied", false)
  , ("metadata_envelope_bridge_premise_supplied", true)
  , ("metadata_adherence_or_admission_premise_supplied", true)
  , ("metadata_adherence_and_bridge_premise_supplied", true)
  ]

/-- The exported literal is exactly the pack's `theoremInventory`. -/
theorem envelopeEvidenceInventory_eq :
    theoremInventory envelopeEvidencePack.{0, 0} = envelopeEvidenceInventory := by
  rfl

example : envelopeEvidencePack.{0, 0}.protocolMachineEnvelopeAdherence?.isSome = true := rfl
example : envelopeEvidencePack.{0, 0}.protocolEnvelopeBridge?.isSome = true := rfl
example : envelopeEvidencePack.{0, 0}.protocolMachineEnvelopeAdmission?.isSome = false := rfl

-- The JSON export encodes exactly the inventory.
#guard inventoryJsonMatches envelopeEvidenceInventory (inventoryToJson envelopeEvidenceInventory)

#guard envelopeEvidenceInventory.lookup "protocol_machine_envelope_adherence" == some true
#guard envelopeEvidenceInventory.lookup "protocol_envelope_bridge" == some true
#guard envelopeEvidenceInventory.lookup "protocol_machine_envelope_admission" == some false

end Examples
end Proofs
end Runtime
