//! Schema versioning helpers for Lean bridge payloads.

/// Current schema version for Lean bridge JSON payloads.
pub const LEAN_BRIDGE_SCHEMA_VERSION: &str = "lean_bridge.v1";

/// Default schema version used by serde when legacy payloads omit the field.
#[must_use]
pub fn default_schema_version() -> String {
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
