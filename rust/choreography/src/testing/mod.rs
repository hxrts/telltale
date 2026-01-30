//! Test harness for choreographic protocols
//!
//! This module provides a fluent API for testing protocol execution,
//! making it easy to set up multi-role tests and verify protocol behavior.
//!
//! # Example
//!
//! ```ignore
//! use telltale_choreography::testing::*;
//!
//! let result = ProtocolTest::builder("AuraConsensus")
//!     .bind_role("Coordinator", coordinator_adapter)
//!     .bind_roles("Witness", &[w1, w2, w3])
//!     .with_params(ConsensusParams { threshold: 2 })
//!     .expect_phases(&["broadcast_execute", "collect_commits"])
//!     .run()
//!     .await?;
//!
//! assert!(result.completed_successfully());
//! assert_eq!(result.phase_count(), 2);
//! ```

pub mod harness;

pub use harness::{ProtocolTest, ProtocolTestBuilder, RoleBinding, TestConfig, TestResult};
