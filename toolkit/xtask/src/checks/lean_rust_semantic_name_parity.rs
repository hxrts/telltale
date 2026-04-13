use std::fs;
use std::path::Path;

use anyhow::{bail, Result};

pub fn run(repo_root: &Path) -> Result<()> {
    let required_surfaces = &[
        "lean/Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean",
        "lean/Runtime/ProtocolMachine/Model/SemanticObjects/AgreementCore.lean",
        "lean/Runtime/ProtocolMachine/Model/SemanticObjects.lean",
        "lean/Runtime/ProtocolMachine/API.lean",
        "rust/machine/src/semantic_objects.rs",
        "rust/machine/src/lib.rs",
        "rust/bridge/src/semantic_objects.rs",
        "lean/Runtime/ProtocolMachine/Runtime/Runner.lean",
        "rust/bridge/src/protocol_machine_runner.rs",
        "rust/bridge/src/protocol_machine_trace.rs",
    ];

    for path in required_surfaces {
        let full = repo_root.join(path);
        if !full.exists() {
            eprintln!("[semantic-name-parity] missing required surface: {path}");
            bail!("lean-rust-semantic-name-parity failed");
        }
    }

    let required_types = &[
        "OwnershipScope",
        "DelegationStatus",
        "OperationInstance",
        "OutstandingEffect",
        "SemanticHandoff",
        "AuthoritativeRead",
        "ObservedRead",
        "MaterializationProof",
        "CanonicalHandle",
        "PublicationEvent",
        "Region",
        "ProgressContract",
        "ProgressTransition",
        "OperationVisibility",
        "AgreementLevel",
        "AgreementRule",
        "AgreementEvidenceKind",
        "FinalizationOutcome",
        "PrestateBinding",
        "AgreementProfile",
        "AgreementContract",
        "AgreementEvidence",
        "AgreementState",
        "ProtocolMachineSemanticObjects",
    ];

    // Build a combined index: name -> list of files that contain it
    let mut file_contents: Vec<(String, String)> = Vec::new();
    for path in required_surfaces {
        let text = fs::read_to_string(repo_root.join(path))?;
        file_contents.push((path.to_string(), text));
    }

    let mut errors: Vec<String> = Vec::new();

    for type_name in required_types {
        let lean_present = file_contents
            .iter()
            .filter(|(p, _)| p.ends_with(".lean"))
            .any(|(_, text)| text.contains(type_name));
        let rust_present = file_contents
            .iter()
            .filter(|(p, _)| p.ends_with(".rs"))
            .any(|(_, text)| text.contains(type_name));

        if !lean_present {
            errors.push(format!(
                "[semantic-name-parity] type {type_name}: not found in any Lean surface file"
            ));
        }
        if !rust_present {
            errors.push(format!(
                "[semantic-name-parity] type {type_name}: not found in any Rust surface file"
            ));
        }
    }

    if !errors.is_empty() {
        for err in &errors {
            eprintln!("{err}");
        }
        bail!(
            "lean-rust-semantic-name-parity failed: {} missing surface(s)",
            errors.len()
        );
    }

    println!("lean-rust-semantic-name-parity: ok");
    Ok(())
}
