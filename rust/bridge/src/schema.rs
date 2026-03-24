//! Schema versioning helpers for Lean bridge payloads.

use serde::Deserialize;

/// Current schema version for Lean bridge JSON payloads.
pub const LEAN_BRIDGE_SCHEMA_VERSION: &str = "lean_bridge.v1";

/// Canonical schema version emitted by this crate.
#[must_use]
pub fn canonical_schema_version() -> String {
    LEAN_BRIDGE_SCHEMA_VERSION.to_string()
}

/// Return true if the schema version is supported by this crate.
#[must_use]
pub fn is_supported_schema_version(version: &str) -> bool {
    version == LEAN_BRIDGE_SCHEMA_VERSION
}

/// Validate a schema version string for a specific payload type.
///
/// # Errors
///
/// Returns `Err` if the version is unsupported.
pub fn ensure_supported_schema_version(version: &str, payload: &str) -> Result<(), String> {
    if is_supported_schema_version(version) {
        Ok(())
    } else {
        Err(format!(
            "unsupported schema_version '{version}' for {payload}; expected '{}'",
            LEAN_BRIDGE_SCHEMA_VERSION
        ))
    }
}

/// Deserialize one Lean bridge schema version and reject unsupported values.
pub fn deserialize_schema_version<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let version = String::deserialize(deserializer)?;
    ensure_supported_schema_version(&version, "Lean bridge payload")
        .map_err(serde::de::Error::custom)?;
    Ok(version)
}
