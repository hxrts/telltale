//! Test utilities for Lean verification integration.
//!
//! This module provides utilities for tests that require the Lean binary,
//! including graceful skipping when the binary is unavailable.

use crate::runner::LeanRunner;

/// Path to the Lean validator binary (relative to workspace root).
pub const LEAN_BINARY_PATH: &str = "lean/.lake/build/bin/telltale_validator";

/// Skip message displayed when Lean binary is unavailable.
pub const LEAN_SKIP_MESSAGE: &str =
    "SKIPPED: Lean binary not available. Run `cd lean && lake build telltale_validator` to enable.";

/// Check if the Lean binary is available for testing.
#[must_use]
pub fn lean_available() -> bool {
    LeanRunner::is_available()
}

/// Macro for conditionally skipping tests that require the Lean binary.
///
/// Place this at the start of a test function to skip gracefully when
/// the Lean binary is not built.
///
/// # Example
///
/// ```ignore
/// #[test]
/// fn test_lean_validation() {
///     skip_without_lean!();
///     // ... rest of test
/// }
/// ```
#[macro_export]
macro_rules! skip_without_lean {
    () => {
        if !$crate::test_utils::lean_available() {
            eprintln!("{}", $crate::test_utils::LEAN_SKIP_MESSAGE);
            return;
        }
    };
}

/// Deterministic seed for property-based tests.
///
/// Using a fixed seed ensures all proptest runs are reproducible.
/// The same seed always generates the same sequence of test cases.
pub const DETERMINISTIC_SEED: [u8; 32] = [
    0x52, 0x75, 0x6D, 0x70, 0x73, 0x74, 0x65, 0x61, // "Rumpstea"
    0x6B, 0x41, 0x75, 0x72, 0x61, 0x4C, 0x65, 0x61, // "kAuraLea"
    0x6E, 0x42, 0x72, 0x69, 0x64, 0x67, 0x65, 0x54, // "nBridgeT"
    0x65, 0x73, 0x74, 0x53, 0x65, 0x65, 0x64, 0x21, // "estSeed!"
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_available_returns_bool() {
        // Just verify it doesn't panic
        let _available = lean_available();
    }

    #[test]
    fn test_deterministic_seed_is_32_bytes() {
        assert_eq!(DETERMINISTIC_SEED.len(), 32);
    }

    #[test]
    fn test_skip_without_lean_macro() {
        // This test always passes - just verifying the macro compiles
        skip_without_lean!();
        // If we get here, Lean is available
    }
}
