#![cfg(not(target_arch = "wasm32"))]

use serde_json::json;
use telltale_bridge::protocol_machine_runner::ProtocolMachineRunner;

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("STRICT_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value == "1")
        .unwrap_or(false)
}

fn protocol_machine_runner() -> ProtocolMachineRunner {
    if strict_protocol_machine_runner_required() {
        ProtocolMachineRunner::require_available();
    }
    ProtocolMachineRunner::try_new().expect(
        "Lean protocol-machine runner not available. Build with: cd lean && lake build protocol_machine_runner",
    )
}

#[test]
fn lean_capability_model_matches_canonical_finalization_shape() {
    let runner = protocol_machine_runner();
    let payload = json!({
        "finalization": {
            "operation_id": "materialization:ready",
            "session": 7,
            "owner_id": "runtime/owner",
            "read_class": "authoritative_only",
            "observed_read_ids": [],
            "authoritative_read_ids": ["Runtime.ready"],
            "proof_ids": ["proof:ready"],
            "canonical_handle_ids": ["handle:ready"],
            "publication_ids": ["publication:ready"],
            "invalidated_by_handoff_ids": [],
            "rejected_publication_ids": []
        },
        "runtime_upgrade": {
            "upgrade_id": "upgrade:1",
            "phase": "committed_cutover",
            "previous_members": ["A"],
            "next_members": ["A", "B"],
            "execution_constraint": "preserve_bundle_profile",
            "ownership_continuity_required": true,
            "pending_effect_treatment": "preserve_pending",
            "canonical_publication_continuity": "preserve_canonical_truth",
            "carried_publication_ids": ["publication:ready"],
            "invalidated_publication_ids": [],
            "carried_obligation_ids": ["obligation:ready"],
            "invalidated_obligation_ids": [],
            "reason": null
        }
    });

    let response = runner
        .inspect_capability_model(&payload)
        .expect("inspectCapabilityModel should execute");

    assert_eq!(
        response["finalization"]["stage"],
        json!("canonical"),
        "Lean finalization facade should classify proof+handle paths as canonical"
    );
    assert_eq!(
        response["artifacts"]["finalization_is_canonical"],
        json!(true),
        "canonical path should be marked canonical in Lean artifacts"
    );
    assert_eq!(
        response["runtime_upgrade"]["phase"],
        json!("committed_cutover"),
        "Lean runtime-upgrade facade should preserve the committed cutover phase"
    );
    assert_eq!(
        response["artifacts"]["runtime_upgrade_is_committed_cutover"],
        json!(true),
        "committed cutover should be exposed as such in Lean artifacts"
    );
}

#[test]
fn lean_capability_model_matches_invalidated_and_rejected_paths() {
    let runner = protocol_machine_runner();
    let payload = json!({
        "finalization": {
            "operation_id": "handoff:9",
            "session": 9,
            "owner_id": "runtime/old-owner",
            "read_class": "mixed",
            "observed_read_ids": ["obs:1"],
            "authoritative_read_ids": ["auth:1"],
            "proof_ids": ["proof:stale"],
            "canonical_handle_ids": ["handle:stale"],
            "publication_ids": ["publication:stale"],
            "invalidated_by_handoff_ids": [9],
            "rejected_publication_ids": []
        },
        "runtime_upgrade": {
            "upgrade_id": "upgrade:2",
            "phase": "rolled_back",
            "previous_members": ["A", "B"],
            "next_members": ["A", "B"],
            "execution_constraint": "mixed_determinism_allowed",
            "ownership_continuity_required": false,
            "pending_effect_treatment": "invalidate_blocked",
            "canonical_publication_continuity": "reissue_canonical_truth",
            "carried_publication_ids": [],
            "invalidated_publication_ids": ["publication:stale"],
            "carried_obligation_ids": [],
            "invalidated_obligation_ids": ["obligation:stale"],
            "reason": "rollback requested"
        }
    });

    let response = runner
        .inspect_capability_model(&payload)
        .expect("inspectCapabilityModel should execute");

    assert_eq!(
        response["finalization"]["stage"],
        json!("invalidated"),
        "handoff invalidation should dominate canonicalization in Lean"
    );
    assert_eq!(
        response["artifacts"]["finalization_is_invalidated"],
        json!(true),
        "invalidated path should be marked invalidated in Lean artifacts"
    );
    assert_eq!(
        response["runtime_upgrade"]["phase"],
        json!("rolled_back"),
        "Lean runtime-upgrade facade should preserve rollback phases"
    );
    assert_eq!(
        response["artifacts"]["runtime_upgrade_is_committed_cutover"],
        json!(false),
        "rolled-back upgrades must not be treated as committed cutovers"
    );
}
