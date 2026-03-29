#![allow(missing_docs)]

use std::fs;
use std::path::PathBuf;

use telltale_bridge::bridge_normalization_ledger;
use telltale_language::ast::{choreography_to_global, AuthorityMetatheoryTier};
use telltale_language::parse_choreography_file;
use telltale_machine::{transported_theorem_boundary, TransportedTheoremUsageClass};

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read_doc(path: &str) -> String {
    fs::read_to_string(repo_root().join(path)).unwrap_or_else(|err| panic!("read {path}: {err}"))
}

fn authority_fixture_path(name: &str) -> PathBuf {
    repo_root()
        .join("rust/runtime/tests/ui/authority_pass")
        .join(format!("{name}.tell"))
}

fn assert_contains_row(doc: &str, row: &str) {
    assert!(
        doc.contains(row),
        "missing expected docs row:\n{row}\n\ndocument excerpt:\n{}",
        &doc[..doc.len().min(4000)]
    );
}

fn yes_no(value: bool) -> &'static str {
    if value {
        "yes"
    } else {
        "no"
    }
}

fn authority_tier_name(tier: AuthorityMetatheoryTier) -> &'static str {
    match tier {
        AuthorityMetatheoryTier::SessionTypedCoordination => "`session_typed_coordination`",
        AuthorityMetatheoryTier::EvidencePublicationSemanticObjects => {
            "`evidence_publication_semantic_objects`"
        }
        AuthorityMetatheoryTier::RuntimeSemanticOnly => "`runtime_semantic_only`",
    }
}

#[test]
fn capability_admission_source_derived_boundary_rows_match_runtime_contracts() {
    let doc = read_doc("docs/25_capability_admission.md");
    assert!(
        doc.contains("Source-Derived Rows"),
        "capability admission doc should explicitly mark source-derived rows"
    );

    for key in [
        "byzantine_safety_characterization",
        "protocol_machine_envelope_adherence",
        "protocol_machine_envelope_admission",
        "protocol_envelope_bridge",
    ] {
        let entry = transported_theorem_boundary()
            .into_iter()
            .find(|entry| entry.key == key)
            .unwrap_or_else(|| panic!("missing transported-theorem boundary entry for {key}"));
        let usage_class = match entry.usage_class {
            TransportedTheoremUsageClass::RuntimeCriticalInstantiatedPremise => {
                "`runtime_critical_instantiated_premise`"
            }
            TransportedTheoremUsageClass::BlackBoxPremiseOnly => "`black_box_premise_only`",
            TransportedTheoremUsageClass::DocumentationBackgroundOnly => {
                "`documentation_background_only`"
            }
        };
        let assumption_boundary = entry
            .assumption_boundary
            .unwrap_or_else(|| "`none`".to_string());
        let row = format!(
            "| `{}` | {} | {} | {} | {} |",
            entry.key,
            usage_class,
            yes_no(entry.consumed_by_rust_runtime_admission),
            yes_no(entry.consumed_by_lean_runtime_gate),
            assumption_boundary
        );
        assert_contains_row(&doc, &row);
    }
}

#[test]
fn authority_language_source_derived_support_matrix_matches_fixture_statuses() {
    let doc = read_doc("docs/34_authority_language_surface.md");
    assert!(
        doc.contains("Source-Derived Support Matrix"),
        "authority language doc should explicitly mark source-derived support matrices"
    );

    for (fixture, label, expected_blocker) in [
        (
            "call_plain_communication",
            "`call` with plain communication",
            None,
        ),
        (
            "choice_observational_binding",
            "`choice` with observational binding",
            None,
        ),
        (
            "loop_authoritative_binding",
            "counted `loop` with authoritative binding",
            None,
        ),
        (
            "recursion_authoritative_binding",
            "recursion with authoritative binding",
            None,
        ),
        (
            "parallel_observational_binding",
            "`par` with observational binding",
            Some("Parallel"),
        ),
        (
            "case_authoritative_binding",
            "`case/of` with authoritative binding",
            Some("Case"),
        ),
        (
            "timeout_observational_binding",
            "`timeout` with observational binding",
            Some("Timeout"),
        ),
    ] {
        let path = authority_fixture_path(fixture);
        let choreography =
            parse_choreography_file(&path).unwrap_or_else(|err| panic!("parse {fixture}: {err}"));
        choreography
            .validate()
            .unwrap_or_else(|err| panic!("validate {fixture}: {err}"));
        let language_status = choreography.language_tier_status();
        let authority_status = choreography.authority_metatheory_status();
        let blocker = match expected_blocker {
            Some(expected_blocker) => {
                let err = choreography_to_global(&choreography)
                    .expect_err("non-theory-convertible fixture must fail conversion");
                assert!(
                    err.to_string().contains(expected_blocker),
                    "{fixture} should report an explicit {expected_blocker} blocker, got {err}"
                );
                format!("`{expected_blocker}`")
            }
            None => {
                choreography_to_global(&choreography)
                    .unwrap_or_else(|err| panic!("convert {fixture} to GlobalType: {err}"));
                "`none`".to_string()
            }
        };

        let row = format!(
            "| {} | {} | {} | {} | {} | {} |",
            label,
            yes_no(language_status.protocol_machine_executable),
            yes_no(language_status.session_projectable),
            yes_no(language_status.theory_convertible),
            authority_tier_name(authority_status.strongest_tier),
            blocker
        );
        assert_contains_row(&doc, &row);
    }
}

#[test]
fn verification_inventory_declares_source_derived_metrics_and_trust_rows() {
    let doc = read_doc("docs/32_testing_verification_inventory.md");

    for needle in [
        "The numeric rows in this section are source-derived and checked by",
        "`scripts/check/verification-inventory.sh`",
        "The rows in this table are source-derived and checked by",
        "`scripts/check/bridge-normalization-ledger.sh`",
        "| Public docs as contract |",
        "## Compiler and Macro Claim Boundary",
        "the current public formal-verification claim does not include any Rust parser,",
        "`tell!` macro expansion are outside the formal claim",
    ] {
        assert!(
            doc.contains(needle),
            "verification inventory should advertise docs-as-contract boundary for {needle}"
        );
    }

    for entry in bridge_normalization_ledger() {
        let row = format!(
            "| {} | {} | {} | {} |",
            entry.surface,
            entry.rule,
            entry.classification.doc_label(),
            entry.rationale
        );
        assert!(
            doc.contains(&row),
            "verification inventory should contain bridge normalization ledger row: {row}"
        );
    }

    assert!(
        !doc.contains("session-status ordering |"),
        "removed bridge normalization rows must stay out of the inventory"
    );
}

#[test]
fn choreographic_dsl_doc_and_macro_docs_exclude_tell_from_formal_claim() {
    let dsl_doc = read_doc("docs/06_choreographic_dsl.md");
    assert!(
        dsl_doc.contains("`tell!` is outside the current formal-verification claim."),
        "DSL doc must explicitly exclude tell! from the current formal claim"
    );

    let macro_lib = read_doc("rust/macros/src/lib.rs");
    assert!(
        macro_lib.contains("not part of the current\n//! formal-verification claim"),
        "macro crate docs must explicitly exclude macros from the current formal claim"
    );

    let macro_choreography = read_doc("rust/macros/src/choreography.rs");
    assert!(
        macro_choreography.contains("This macro is intentionally outside the current formal-verification claim."),
        "tell! macro implementation docs must explicitly exclude tell! from the current formal claim"
    );

    let language_lib = read_doc("rust/language/src/lib.rs");
    assert!(
        language_lib.contains("intentionally outside the current formal-verification claim"),
        "language crate docs must explicitly exclude Rust compiler-pipeline APIs from the current formal claim"
    );

    let runtime_compiler = read_doc("rust/runtime/src/compiler/mod.rs");
    assert!(
        runtime_compiler.contains("intentionally outside the current\n//! formal-verification claim"),
        "runtime compiler module docs must explicitly exclude compiler helpers from the current formal claim"
    );

    let architecture_doc = read_doc("docs/03_architecture.md");
    assert!(
        architecture_doc.contains("The current formal-verification claim is narrower than this full architecture"),
        "architecture doc must explicitly scope the formal claim below the full Rust compiler/runtime architecture"
    );
}
