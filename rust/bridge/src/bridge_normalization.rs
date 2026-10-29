//! Canonical ledger for the Rust/Lean bridge normalization trust surface.
//!
//! This module exists to keep the remaining trusted bridge behavior small,
//! explicit, and source-derived. Documentation and shell gates should point at
//! this ledger instead of maintaining parallel hand-written classifications.
//!
//! Compatibility helpers that are outside the strict claim-critical path should
//! not appear here.

/// Classification for one bridge trust-surface entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BridgeNormalizationClassification {
    /// Irreducible comparison logic that preserves protocol semantics while
    /// abstracting away non-semantic scheduling details.
    IrreducibleTrustedComparisonLogic,
}

impl BridgeNormalizationClassification {
    /// Stable wording used in the verification inventory.
    #[must_use]
    pub const fn doc_label(self) -> &'static str {
        match self {
            Self::IrreducibleTrustedComparisonLogic => "irreducible trusted comparison logic",
        }
    }
}

/// Stable backfill path identifiers for schema-version compatibility shims.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchemaVersionBackfillPath {
    Root,
    TraceEvent,
    SessionStatus,
    StepEvent,
    SemanticObjects,
}

impl SchemaVersionBackfillPath {
    /// Stable label used by tests and docs.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Root => "root",
            Self::TraceEvent => "trace event",
            Self::SessionStatus => "session status",
            Self::StepEvent => "step event",
            Self::SemanticObjects => "semantic objects",
        }
    }
}

/// Canonical backfill paths allowed for schema-version compatibility.
pub const SCHEMA_VERSION_BACKFILL_PATHS: &[SchemaVersionBackfillPath] = &[
    SchemaVersionBackfillPath::Root,
    SchemaVersionBackfillPath::TraceEvent,
    SchemaVersionBackfillPath::SessionStatus,
    SchemaVersionBackfillPath::StepEvent,
    SchemaVersionBackfillPath::SemanticObjects,
];

/// One explicitly permitted bridge normalization rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BridgeNormalizationEntry {
    pub surface: &'static str,
    pub rule: &'static str,
    pub classification: BridgeNormalizationClassification,
    pub rationale: &'static str,
    pub artifacts: &'static [&'static str],
}

/// Canonical bridge normalization ledger.
#[must_use]
pub fn bridge_normalization_ledger() -> Vec<BridgeNormalizationEntry> {
    vec![BridgeNormalizationEntry {
        surface: "semantic-audit tick normalization",
        rule: "Normalize only `tick`, and only per extracted session id",
        classification: BridgeNormalizationClassification::IrreducibleTrustedComparisonLogic,
        rationale: "Absolute cross-session scheduling order is not semantic protocol truth. Per-session observable order is.",
        artifacts: &[
            "rust/bridge/src/protocol_machine_trace.rs",
            "rust/bridge/tests/protocol_machine_correspondence_tests.rs",
            "rust/bridge/tests/protocol_machine_differential_steps.rs",
        ],
    }, BridgeNormalizationEntry {
        surface: "single nominal occurrence comparison",
        rule: "Relate only the validated original nominal occurrence ID and preserve exact original-or-plus-one reply relation/refusal; never normalize ticks, typed application results, lifecycle or continuation",
        classification: BridgeNormalizationClassification::IrreducibleTrustedComparisonLogic,
        rationale: "Rust also issues non-nominal observational effects, so its absolute counter namespace differs from the selected executable model. Each side must retain exactly one actual nominal occurrence with consistent operation/request references before the comparison relates that ID. Raw outputs are unchanged.",
        artifacts: &[
            "rust/bridge/src/nominal_image.rs",
            "rust/bridge/tests/support/nominal_image_correspondence.rs",
            "lean/Runtime/Tests/NominalImageRunner.lean",
        ],
    }]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bridge_normalization_contract_ledger_is_minimal_and_explicit() {
        let ledger = bridge_normalization_ledger();
        assert_eq!(ledger.len(), 2);

        assert_eq!(ledger[1].surface, "single nominal occurrence comparison");
        assert!(ledger[1].rule.contains("never normalize ticks"));
        let tick = &ledger[0];
        assert_eq!(tick.surface, "semantic-audit tick normalization");
        assert_eq!(
            tick.rule,
            "Normalize only `tick`, and only per extracted session id"
        );
        assert_eq!(
            tick.classification,
            BridgeNormalizationClassification::IrreducibleTrustedComparisonLogic
        );
    }

    #[test]
    fn bridge_normalization_contract_schema_backfill_paths_are_exact() {
        let labels: Vec<_> = SCHEMA_VERSION_BACKFILL_PATHS
            .iter()
            .map(|path| path.label())
            .collect();
        assert_eq!(
            labels,
            vec![
                "root",
                "trace event",
                "session status",
                "step event",
                "semantic objects"
            ]
        );
    }
}
