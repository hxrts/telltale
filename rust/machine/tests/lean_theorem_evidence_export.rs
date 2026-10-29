#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Lean theorem-pack evidence export drives Rust envelope admission.
//!
//! Runs `lean/.lake/build/bin/theorem_evidence_export` (if built), parses its
//! JSON inventory with `LeanEvidenceInventory::from_json_str`, and checks that
//! admission follows exactly the exported Lean flags.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use telltale_machine::{
    execution_profile_supported, runtime_execution_profile, LeanEvidenceInventory,
    OutputConditionPolicy, ProtocolMachineConfig, ProtocolMachineExecutionProfile,
    RuntimeContracts, LEAN_ENVELOPE_EVIDENCE_KEYS,
};

fn strict_evidence_export_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_THEOREM_EVIDENCE_EXPORT")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn evidence_export_path() -> Option<PathBuf> {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = crate_dir
        .parent()
        .and_then(Path::parent)
        .map(|root| root.join("lean/.lake/build/bin/theorem_evidence_export"))?;
    path.is_file().then_some(path)
}

fn exported_inventory_json() -> Option<String> {
    let Some(path) = evidence_export_path() else {
        assert!(
            !strict_evidence_export_required(),
            "strict evidence export verification is enabled but the Lean exe is unavailable"
        );
        eprintln!(
            "Lean theorem_evidence_export not available. Build with: cd lean && lake build theorem_evidence_export"
        );
        return None;
    };
    let output = Command::new(path)
        .output()
        .expect("run theorem_evidence_export");
    assert!(output.status.success(), "theorem_evidence_export failed");
    Some(String::from_utf8(output.stdout).expect("utf8 inventory"))
}

#[test]
fn lean_exported_inventory_drives_envelope_admission() {
    let Some(json) = exported_inventory_json() else {
        return;
    };
    let raw: BTreeMap<String, bool> = serde_json::from_str(&json).expect("inventory object");
    let evidence = LeanEvidenceInventory::from_json_str(&json).expect("inventory parses");

    for key in LEAN_ENVELOPE_EVIDENCE_KEYS {
        let flag = *raw.get(key).expect("envelope key exported by Lean");
        assert!(flag, "concrete Lean pack carries the {key} profile");
        assert_eq!(evidence.admits(key), flag, "admission for {key}");
    }

    let profile = ProtocolMachineExecutionProfile::full().with_lean_evidence(evidence);
    assert_eq!(
        profile.supports_protocol_machine_envelope_adherence(),
        raw["protocol_machine_envelope_adherence"]
    );
    assert_eq!(
        profile.supports_protocol_machine_envelope_admission(),
        raw["protocol_machine_envelope_admission"]
    );
    assert_eq!(
        profile.supports_protocol_envelope_bridge(),
        raw["protocol_envelope_bridge"]
    );

    let bridge_cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    };
    let full_contracts = RuntimeContracts::full();
    for contracts in [None, Some(&full_contracts)] {
        let required = runtime_execution_profile(&bridge_cfg, contracts);
        let expected = LEAN_ENVELOPE_EVIDENCE_KEYS.iter().all(|key| {
            let needed = required
                .theorem_pack_eligibility
                .iter()
                .any(|(k, enabled)| k == key && *enabled);
            !needed || raw[*key]
        });
        let structural = required
            .fairness_assumptions
            .is_subset(&profile.fairness_assumptions)
            && required
                .admissibility_classes
                .is_subset(&profile.admissibility_classes)
            && required
                .escalation_window_classes
                .is_subset(&profile.escalation_window_classes);
        assert_eq!(
            execution_profile_supported(&profile, &bridge_cfg, contracts),
            structural && expected,
            "admission must follow exported Lean flags (contracts: {})",
            contracts.is_some()
        );
    }
}
