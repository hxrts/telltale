import Lean.Data.Json
import Runtime.Proofs.CapabilityModel
import Runtime.Proofs.TheoremPack.AdmissionBoundary

/-! # Protocol-Machine Validator

Small JSON validator entry point for capability-model inspection, protocol-bundle
admission checks, and reconfiguration-transition validation. This is split out
from the executable runner so the native runner does not need to link the full
capability/theorem-pack surface on macOS.
-/

set_option autoImplicit false

open Lean (Json)

def bridgeSchemaVersion : Json :=
  Json.str "lean_bridge.v1"

def structuredError (code path message : String) : Json :=
  Json.mkObj
    [ ("code", Json.str code)
    , ("path", Json.str path)
    , ("message", Json.str message) ]

def jsonStringList (value : Json) : Except String (List String) := do
  let arr ← value.getArr?
  arr.toList.mapM Json.getStr?

def jsonNatList (value : Json) : Except String (List Nat) := do
  let arr ← value.getArr?
  arr.toList.mapM Json.getNat?

def optionalNatField? (value : Json) (field : String) : Option Nat :=
  match value.getObjVal? field with
  | .ok fieldValue =>
      match fieldValue.getNat? with
      | .ok n => some n
      | .error _ => none
  | .error _ => none

def optionalBoolField? (value : Json) (field : String) : Option Bool :=
  match value.getObjVal? field with
  | .ok fieldValue =>
      match fieldValue.getBool? with
      | .ok b => some b
      | .error _ => none
  | .error _ => none

def optionalStringField? (value : Json) (field : String) : Option String :=
  match value.getObjVal? field with
  | .ok fieldValue =>
      match fieldValue.getStr? with
      | .ok s => some s
      | .error _ => none
  | .error _ => none

def optionalStringListField (value : Json) (field : String) : List String :=
  match value.getObjVal? field with
  | .ok fieldValue => (jsonStringList fieldValue).toOption.getD []
  | .error _ => []

def optionalNatListField (value : Json) (field : String) : List Nat :=
  match value.getObjVal? field with
  | .ok fieldValue => (jsonNatList fieldValue).toOption.getD []
  | .error _ => []

def parseFinalizationReadClass (value : String) :
    Except String Runtime.Proofs.FinalizationReadClass :=
  match value with
  | "none" => .ok .none
  | "observed_only" => .ok .observedOnly
  | "authoritative_only" => .ok .authoritativeOnly
  | "mixed" => .ok .mixed
  | other => .error s!"unknown finalization read class: {other}"

def finalizationReadClassJson
    (value : Runtime.Proofs.FinalizationReadClass) : Json :=
  Json.str <|
    match value with
    | .none => "none"
    | .observedOnly => "observed_only"
    | .authoritativeOnly => "authoritative_only"
    | .mixed => "mixed"

def finalizationStageJson
    (value : Runtime.Proofs.FinalizationStage) : Json :=
  Json.str <|
    match value with
    | .observed => "observed"
    | .authoritative => "authoritative"
    | .materialized => "materialized"
    | .canonical => "canonical"
    | .invalidated => "invalidated"
    | .rejected => "rejected"

def parseTransitionArtifactPhase (value : String) :
    Except String Runtime.Proofs.TransitionArtifactPhase :=
  match value with
  | "staged" => .ok .staged
  | "admitted" => .ok .admitted
  | "committed_cutover" => .ok .committedCutover
  | "rolled_back" => .ok .rolledBack
  | "failed" => .ok .failed
  | other => .error s!"unknown transition artifact phase: {other}"

def transitionArtifactPhaseJson
    (value : Runtime.Proofs.TransitionArtifactPhase) : Json :=
  Json.str <|
    match value with
    | .staged => "staged"
    | .admitted => "admitted"
    | .committedCutover => "committed_cutover"
    | .rolledBack => "rolled_back"
    | .failed => "failed"

def parsePendingEffectTreatment (value : String) :
    Except String Runtime.Proofs.PendingEffectTreatment :=
  match value with
  | "preserve_pending" => .ok .preservePending
  | "invalidate_blocked" => .ok .invalidateBlocked
  | other => .error s!"unknown pending effect treatment: {other}"

def pendingEffectTreatmentJson
    (value : Runtime.Proofs.PendingEffectTreatment) : Json :=
  Json.str <|
    match value with
    | .preservePending => "preserve_pending"
    | .invalidateBlocked => "invalidate_blocked"

def parseCanonicalPublicationContinuity (value : String) :
    Except String Runtime.Proofs.CanonicalPublicationContinuity :=
  match value with
  | "preserve_canonical_truth" => .ok .preserveCanonicalTruth
  | "reissue_canonical_truth" => .ok .reissueCanonicalTruth
  | other => .error s!"unknown canonical publication continuity: {other}"

def canonicalPublicationContinuityJson
    (value : Runtime.Proofs.CanonicalPublicationContinuity) : Json :=
  Json.str <|
    match value with
    | .preserveCanonicalTruth => "preserve_canonical_truth"
    | .reissueCanonicalTruth => "reissue_canonical_truth"

def parseRuntimeUpgradeExecutionConstraint (value : String) :
    Except String Runtime.Proofs.RuntimeUpgradeExecutionConstraint :=
  match value with
  | "preserve_bundle_profile" => .ok .preserveBundleProfile
  | "mixed_determinism_allowed" => .ok .mixedDeterminismAllowed
  | other => .error s!"unknown runtime upgrade execution constraint: {other}"

def runtimeUpgradeExecutionConstraintJson
    (value : Runtime.Proofs.RuntimeUpgradeExecutionConstraint) : Json :=
  Json.str <|
    match value with
    | .preserveBundleProfile => "preserve_bundle_profile"
    | .mixedDeterminismAllowed => "mixed_determinism_allowed"

def finalizationPathJson (path : Runtime.Proofs.FinalizationPath) : Json :=
  Json.mkObj
    [ ("operation_id", Json.str path.operationId)
    , ("session", path.session.map Json.num |>.getD Json.null)
    , ("owner_id", path.ownerId.map Json.str |>.getD Json.null)
    , ("read_class", finalizationReadClassJson path.readClass)
    , ("stage", finalizationStageJson path.stage)
    , ("observed_read_ids", Json.arr <| path.observedReadIds.map Json.str |>.toArray)
    , ("authoritative_read_ids",
        Json.arr <| path.authoritativeReadIds.map Json.str |>.toArray)
    , ("proof_ids", Json.arr <| path.proofIds.map Json.str |>.toArray)
    , ("canonical_handle_ids",
        Json.arr <| path.canonicalHandleIds.map Json.str |>.toArray)
    , ("publication_ids", Json.arr <| path.publicationIds.map Json.str |>.toArray)
    , ("invalidated_by_handoff_ids",
        Json.arr <| path.invalidatedByHandoffIds.map Json.num |>.toArray)
    , ("rejected_publication_ids",
        Json.arr <| path.rejectedPublicationIds.map Json.str |>.toArray) ]

def runtimeUpgradeCompatibilityJson
    (compatibility : Runtime.Proofs.RuntimeUpgradeCompatibility) : Json :=
  Json.mkObj
    [ ("execution_constraint",
        runtimeUpgradeExecutionConstraintJson compatibility.executionConstraint)
    , ("ownership_continuity_required",
        Json.bool compatibility.ownershipContinuityRequired)
    , ("pending_effect_treatment",
        pendingEffectTreatmentJson compatibility.pendingEffectTreatment)
    , ("canonical_publication_continuity",
        canonicalPublicationContinuityJson compatibility.canonicalPublicationContinuity) ]

def runtimeUpgradeArtifactJson
    (artifact : Runtime.Proofs.RuntimeUpgradeArtifact) : Json :=
  Json.mkObj
    [ ("upgrade_id", Json.str artifact.upgradeId)
    , ("phase", transitionArtifactPhaseJson artifact.phase)
    , ("previous_members", Json.arr <| artifact.previousMembers.map Json.str |>.toArray)
    , ("next_members", Json.arr <| artifact.nextMembers.map Json.str |>.toArray)
    , ("compatibility", runtimeUpgradeCompatibilityJson artifact.compatibility)
    , ("carried_publication_ids",
        Json.arr <| artifact.carriedPublicationIds.map Json.str |>.toArray)
    , ("invalidated_publication_ids",
        Json.arr <| artifact.invalidatedPublicationIds.map Json.str |>.toArray)
    , ("carried_obligation_ids",
        Json.arr <| artifact.carriedObligationIds.map Json.str |>.toArray)
    , ("invalidated_obligation_ids",
        Json.arr <| artifact.invalidatedObligationIds.map Json.str |>.toArray)
    , ("reason", artifact.reason.map Json.str |>.getD Json.null) ]

def inspectCapabilityModelResponse (payload : Json) : Json :=
  let finalizationPayload := payload.getObjValD "finalization"
  let runtimeUpgradePayload := payload.getObjValD "runtime_upgrade"
  match parseFinalizationReadClass
      ((optionalStringField? finalizationPayload "read_class").getD "none"),
    parseTransitionArtifactPhase
      ((optionalStringField? runtimeUpgradePayload "phase").getD "staged"),
    parseRuntimeUpgradeExecutionConstraint
      ((optionalStringField? runtimeUpgradePayload "execution_constraint").getD
        "preserve_bundle_profile"),
    parsePendingEffectTreatment
      ((optionalStringField? runtimeUpgradePayload "pending_effect_treatment").getD
        "preserve_pending"),
    parseCanonicalPublicationContinuity
      ((optionalStringField? runtimeUpgradePayload "canonical_publication_continuity").getD
        "preserve_canonical_truth") with
  | .ok readClass, .ok phase, .ok executionConstraint, .ok pendingEffects, .ok continuity =>
      let finalization :=
        Runtime.Proofs.deriveFinalizationPath
          ((optionalStringField? finalizationPayload "operation_id").getD "operation")
          (optionalNatField? finalizationPayload "session")
          (optionalStringField? finalizationPayload "owner_id")
          readClass
          (optionalStringListField finalizationPayload "observed_read_ids")
          (optionalStringListField finalizationPayload "authoritative_read_ids")
          (optionalStringListField finalizationPayload "proof_ids")
          (optionalStringListField finalizationPayload "canonical_handle_ids")
          (optionalStringListField finalizationPayload "publication_ids")
          (optionalNatListField finalizationPayload "invalidated_by_handoff_ids")
          (optionalStringListField finalizationPayload "rejected_publication_ids")
      let runtimeUpgrade : Runtime.Proofs.RuntimeUpgradeArtifact :=
        { upgradeId := (optionalStringField? runtimeUpgradePayload "upgrade_id").getD "upgrade"
        , phase := phase
        , previousMembers := optionalStringListField runtimeUpgradePayload "previous_members"
        , nextMembers := optionalStringListField runtimeUpgradePayload "next_members"
        , compatibility :=
            { executionConstraint := executionConstraint
            , ownershipContinuityRequired :=
                (optionalBoolField? runtimeUpgradePayload "ownership_continuity_required").getD true
            , pendingEffectTreatment := pendingEffects
            , canonicalPublicationContinuity := continuity }
        , carriedPublicationIds :=
            optionalStringListField runtimeUpgradePayload "carried_publication_ids"
        , invalidatedPublicationIds :=
            optionalStringListField runtimeUpgradePayload "invalidated_publication_ids"
        , carriedObligationIds :=
            optionalStringListField runtimeUpgradePayload "carried_obligation_ids"
        , invalidatedObligationIds :=
            optionalStringListField runtimeUpgradePayload "invalidated_obligation_ids"
        , reason := optionalStringField? runtimeUpgradePayload "reason" }
      Json.mkObj
        [ ("schema_version", bridgeSchemaVersion)
        , ("finalization", finalizationPathJson finalization)
        , ("runtime_upgrade", runtimeUpgradeArtifactJson runtimeUpgrade)
        , ("artifacts", Json.mkObj
            [ ("finalization_is_canonical", Json.bool (decide (finalization.stage = .canonical)))
            , ("finalization_is_invalidated", Json.bool (decide (finalization.stage = .invalidated)))
            , ("runtime_upgrade_is_committed_cutover",
                Json.bool (decide (runtimeUpgrade.phase = .committedCutover))) ]) ]
  | .error err, _, _, _, _
  | _, .error err, _, _, _
  | _, _, .error err, _, _
  | _, _, _, .error err, _
  | _, _, _, _, .error err =>
      Json.mkObj
        [ ("schema_version", bridgeSchemaVersion)
        , ("errors", Json.arr #[structuredError "capability_model.invalid_payload" "payload" err]) ]

def transportedTheoremUsageClassJson
    (usage : Runtime.Proofs.TransportedTheoremUsageClass) : Json :=
  Json.str <|
    match usage with
    | .blackBoxPremiseOnly => "black_box_premise_only"
    | .runtimeCriticalInstantiatedPremise => "runtime_critical_instantiated_premise"
    | .documentationBackgroundOnly => "documentation_background_only"

def transportedTheoremBoundaryJson : Json :=
  Json.arr <|
    (Runtime.Proofs.transportedTheoremBoundaryInventory.map
      (fun (entry : Runtime.Proofs.TransportedTheoremBoundaryEntry) =>
        Json.mkObj <|
          [ ("key", Json.str entry.key)
          , ("usage_class", transportedTheoremUsageClassJson entry.usageClass)
          , ("consumed_by_rust_runtime_admission",
              Json.bool entry.consumedByRustRuntimeAdmission)
          , ("consumed_by_lean_runtime_gate",
              Json.bool entry.consumedByLeanRuntimeGate)
          ] ++
          match entry.assumptionBoundary? with
          | some assumption => [("assumption_boundary", Json.str assumption)]
          | none => [] )).toArray

def runtimeCriticalTransportedTheoremKeysJson : Json :=
  Json.arr <|
    Runtime.Proofs.rustRuntimeCriticalTransportedTheoremKeys.map Json.str
      |>.toArray

def verifyProtocolBundleErrors (payload : Json) : List Json :=
  let claims := payload.getObjValD "claims"
  let distributed := claims.getObjValD "distributed"
  let liveness := claims.getObjValD "liveness"
  let quorumErrors :=
  let quorumGeometry := distributed.getObjValD "quorum_geometry"
  match (
    optionalNatField? quorumGeometry "n",
    optionalNatField? quorumGeometry "quorum_size",
    optionalNatField? quorumGeometry "intersection_size"
  ) with
  | (some n, some quorumSize, some intersectionSize) =>
      if intersectionSize = 0 || 2 * quorumSize ≤ n then
        [structuredError
          "bundle.bad_quorum"
          "claims.distributed.quorum_geometry"
          "quorum geometry must guarantee non-empty intersection and majority overlap"]
      else
        []
  | _ => []

  let progressRequired := (optionalBoolField? liveness "progress_required").getD false
  let scheduler := optionalStringField? liveness "scheduler"
  let flp := distributed.getObjValD "flp"
  let deadlockErrors := match (
    optionalNatField? flp "crash_bound",
    optionalBoolField? flp "requires_determinism",
    scheduler
  ) with
  | (some crashBound, some true, some "Cooperative") =>
      if progressRequired && crashBound > 0 then
        [structuredError
          "bundle.deadlock_risk"
          "claims.liveness"
          "cooperative progress claims with crash-bound FLP assumptions are rejected in the executable verifier"]
      else
        []
  | _ => []

  let partialSynchrony := distributed.getObjValD "partial_synchrony"
  let responsiveness := distributed.getObjValD "responsiveness"
  let unboundedWaitErrors := match (
    optionalStringField? partialSynchrony "timing",
    optionalNatField? partialSynchrony "delta_bound",
    optionalBoolField? responsiveness "requires_stable_period"
  ) with
  | (some "Asynchronous", none, _) =>
      if progressRequired then
        [structuredError
          "bundle.unbounded_wait"
          "claims.distributed.partial_synchrony"
          "progress-required bundles must provide a bounded synchrony window"]
      else
        []
  | _ => []

  quorumErrors ++ deadlockErrors ++ unboundedWaitErrors

def verifyProtocolBundleResponse (payload : Json) : Json :=
  let errors := verifyProtocolBundleErrors payload
  Json.mkObj
    [ ("valid", Json.bool errors.isEmpty)
    , ("errors", Json.arr errors.toArray)
    , ("artifacts", Json.mkObj
        [ ("mode", Json.str "deterministic_bundle_verifier")
        , ("error_count", Json.num errors.length)
        , ("transported_theorem_boundary", transportedTheoremBoundaryJson)
        , ("rust_runtime_critical_transport_theorem_keys",
            runtimeCriticalTransportedTheoremKeysJson)
        , ("runtime_critical_transport_theorems_explicit",
            Json.bool Runtime.Proofs.runtimeCriticalTransportedTheoremsExplicit)
        ]) ]

def sortedUniqueStrings (items : List String) : List String :=
  (items.eraseDups.toArray.qsort (fun left right => left < right)).toList

def memberDifferences (left right : List String) : List String :=
  left.filter (fun item => !(right.contains item))

def validateReconfigurationTransitionResponse (payload : Json) : Json :=
  let artifactId := (optionalStringField? payload "artifact_id").getD "reconfiguration"
  let policy := payload.getObjValD "policy"
  let startingEpoch := (optionalNatField? payload "starting_epoch").getD 0
  let dynamicMembership := (optionalBoolField? policy "dynamic_membership").getD false
  let overlapRequired := (optionalBoolField? policy "overlap_required").getD false
  let previousMembers := sortedUniqueStrings <| (jsonStringList (payload.getObjValD "previous_members")).toOption.getD []
  let nextMembers := sortedUniqueStrings <| (jsonStringList (payload.getObjValD "next_members")).toOption.getD []
  let overlapPreserved := previousMembers.isEmpty ||
    previousMembers.any (fun member => nextMembers.contains member)
  let errors :=
    (if !dynamicMembership then
      [structuredError
        "reconfiguration.disabled"
        "policy.dynamic_membership"
        "dynamic membership must be enabled for a reconfiguration transition"]
    else []) ++
    (if nextMembers.isEmpty then
      [structuredError
        "reconfiguration.empty_membership"
        "next_members"
        "reconfiguration transitions must preserve a non-empty membership set"]
    else []) ++
    (if overlapRequired && !overlapPreserved then
      [structuredError
        "reconfiguration.overlap_required"
        "next_members"
        "overlap-required reconfiguration transitions must preserve at least one member"]
    else [])
  let event :=
    Json.mkObj
      [ ("artifact_id", Json.str artifactId)
      , ("epoch", Json.num (Nat.succ startingEpoch))
      , ("previous_members", Json.arr <| previousMembers.map Json.str |>.toArray)
      , ("next_members", Json.arr <| nextMembers.map Json.str |>.toArray)
      , ("added_members",
          Json.arr <| (memberDifferences nextMembers previousMembers).map Json.str |>.toArray)
      , ("removed_members",
          Json.arr <| (memberDifferences previousMembers nextMembers).map Json.str |>.toArray)
      , ("overlap_preserved", Json.bool overlapPreserved)
      , ("dynamic_membership", Json.bool dynamicMembership)
      , ("overlap_required", Json.bool overlapRequired) ]
  Json.mkObj
    [ ("valid", Json.bool errors.isEmpty)
    , ("errors", Json.arr errors.toArray)
    , ("artifacts", Json.mkObj
        [ ("mode", Json.str "deterministic_reconfiguration_validator")
        , ("event", event) ]) ]

def dispatchOperation (operation : String) (payload : Json) : IO Unit := do
  match operation with
  | "verifyProtocolBundle" =>
      IO.println (verifyProtocolBundleResponse payload).compress
  | "validateReconfigurationTransition" =>
      IO.println (validateReconfigurationTransitionResponse payload).compress
  | "inspectCapabilityModel" =>
      IO.println (inspectCapabilityModelResponse payload).compress
  | other =>
      throw (IO.userError s!"unsupported operation: {other}")

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let json ←
    match Json.parse input with
    | .error e => throw (IO.userError s!"invalid JSON: {e}")
    | .ok j => pure j
  let operation ←
    match json.getObjValAs? String "operation" with
    | .ok op => pure op
    | .error e => throw (IO.userError s!"missing operation: {e}")
  let payload := json.getObjValD "payload"
  dispatchOperation operation payload
