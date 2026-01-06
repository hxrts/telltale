//! Integration tests for role family resolution.
//!
//! Tests for:
//! - Multi-witness threshold signature protocol
//! - Broadcast with parallel execution
//! - Role family constraint validation

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_aura_choreography::effects::{ChoreographyError, LabelId, RoleId};
use rumpsteak_aura_choreography::identifiers::RoleName;
use rumpsteak_aura_choreography::runtime::adapter::ChoreographicAdapter;
use rumpsteak_aura_choreography::runtime::test_adapter::TestAdapter;
use rumpsteak_aura_choreography::topology::{RoleFamilyConstraint, Topology};
use serde::{Deserialize, Serialize};

// ============================================================================
// Test Role and Label Setup
// ============================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum ThresholdRole {
    Coordinator,
    Witness(u32),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum ThresholdLabel {
    Sign,
    Abort,
}

impl LabelId for ThresholdLabel {
    fn as_str(&self) -> &'static str {
        match self {
            ThresholdLabel::Sign => "Sign",
            ThresholdLabel::Abort => "Abort",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "Sign" => Some(ThresholdLabel::Sign),
            "Abort" => Some(ThresholdLabel::Abort),
            _ => None,
        }
    }
}

impl RoleId for ThresholdRole {
    type Label = ThresholdLabel;

    fn role_name(&self) -> RoleName {
        match self {
            ThresholdRole::Coordinator => RoleName::from_static("Coordinator"),
            ThresholdRole::Witness(_) => RoleName::from_static("Witness"),
        }
    }

    fn role_index(&self) -> Option<u32> {
        match self {
            ThresholdRole::Witness(idx) => Some(*idx),
            _ => None,
        }
    }
}

// ============================================================================
// Test Message Types
// ============================================================================

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct SignRequest {
    message_hash: Vec<u8>,
    nonce: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct PartialSignature {
    witness_id: u32,
    signature_share: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct BroadcastMessage {
    content: String,
    sequence: u32,
}

// ============================================================================
// Threshold Signature Integration Tests
// ============================================================================

#[tokio::test]
async fn test_threshold_signature_broadcast() {
    // Create coordinator adapter with 5 witnesses
    let mut coordinator = TestAdapter::new(ThresholdRole::Coordinator).with_family(
        "Witness",
        vec![
            ThresholdRole::Witness(0),
            ThresholdRole::Witness(1),
            ThresholdRole::Witness(2),
            ThresholdRole::Witness(3),
            ThresholdRole::Witness(4),
        ],
    );

    // Resolve all witnesses
    let witnesses = coordinator.resolve_family("Witness").unwrap();
    assert_eq!(witnesses.len(), 5);

    // Broadcast signing request to all witnesses
    let request = SignRequest {
        message_hash: vec![0xAB; 32],
        nonce: 12345,
    };

    coordinator
        .broadcast(&witnesses, request.clone())
        .await
        .unwrap();

    // Verify all messages were sent
    let sent = coordinator.sent_messages();
    let key = ("Coordinator".to_string(), "Witness".to_string());
    let messages = sent.get(&key).unwrap();
    assert_eq!(messages.len(), 5, "Should have sent to all 5 witnesses");
}

#[tokio::test]
async fn test_threshold_signature_collect() {
    // Create coordinator adapter
    let mut coordinator = TestAdapter::new(ThresholdRole::Coordinator).with_family(
        "Witness",
        vec![
            ThresholdRole::Witness(0),
            ThresholdRole::Witness(1),
            ThresholdRole::Witness(2),
        ],
    );

    // Queue responses from witnesses (simulating their responses)
    for i in 0..3 {
        let sig = PartialSignature {
            witness_id: i,
            signature_share: vec![i as u8; 64],
        };
        coordinator.queue_typed_message(ThresholdRole::Witness(i), ThresholdRole::Coordinator, sig);
    }

    // Collect responses from all witnesses
    let witnesses = coordinator.resolve_family("Witness").unwrap();
    let responses: Vec<PartialSignature> = coordinator.collect(&witnesses).await.unwrap();

    assert_eq!(responses.len(), 3);
    assert_eq!(responses[0].witness_id, 0);
    assert_eq!(responses[1].witness_id, 1);
    assert_eq!(responses[2].witness_id, 2);
}

#[tokio::test]
async fn test_threshold_signature_range() {
    // Test with range resolution: only first 3 witnesses participate
    let coordinator = TestAdapter::new(ThresholdRole::Coordinator).with_family(
        "Witness",
        vec![
            ThresholdRole::Witness(0),
            ThresholdRole::Witness(1),
            ThresholdRole::Witness(2),
            ThresholdRole::Witness(3),
            ThresholdRole::Witness(4),
        ],
    );

    // Resolve range [0, 3) - threshold of 3 witnesses
    let threshold_witnesses = coordinator.resolve_range("Witness", 0, 3).unwrap();
    assert_eq!(threshold_witnesses.len(), 3);
    assert_eq!(threshold_witnesses[0], ThresholdRole::Witness(0));
    assert_eq!(threshold_witnesses[1], ThresholdRole::Witness(1));
    assert_eq!(threshold_witnesses[2], ThresholdRole::Witness(2));
}

// ============================================================================
// Broadcast Integration Tests
// ============================================================================

#[tokio::test]
async fn test_broadcast_to_all_workers() {
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum WorkerRole {
        Manager,
        Worker(u32),
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum WorkerLabel {
        Task,
        Done,
    }

    impl LabelId for WorkerLabel {
        fn as_str(&self) -> &'static str {
            match self {
                WorkerLabel::Task => "Task",
                WorkerLabel::Done => "Done",
            }
        }

        fn from_str(label: &str) -> Option<Self> {
            match label {
                "Task" => Some(WorkerLabel::Task),
                "Done" => Some(WorkerLabel::Done),
                _ => None,
            }
        }
    }

    impl RoleId for WorkerRole {
        type Label = WorkerLabel;

        fn role_name(&self) -> RoleName {
            match self {
                WorkerRole::Manager => RoleName::from_static("Manager"),
                WorkerRole::Worker(_) => RoleName::from_static("Worker"),
            }
        }

        fn role_index(&self) -> Option<u32> {
            match self {
                WorkerRole::Worker(idx) => Some(*idx),
                _ => None,
            }
        }
    }

    // Create manager with 10 workers
    let mut manager = TestAdapter::new(WorkerRole::Manager)
        .with_family("Worker", (0..10).map(WorkerRole::Worker).collect());

    // Broadcast work assignment to all workers
    let workers = manager.resolve_family("Worker").unwrap();
    assert_eq!(workers.len(), 10);

    let task = BroadcastMessage {
        content: "Process batch 42".to_string(),
        sequence: 1,
    };

    manager.broadcast(&workers, task).await.unwrap();

    // Verify broadcast sent to all
    let sent = manager.sent_messages();
    let key = ("Manager".to_string(), "Worker".to_string());
    let messages = sent.get(&key).unwrap();
    assert_eq!(messages.len(), 10);
}

// ============================================================================
// Topology Role Constraint Tests
// ============================================================================

#[test]
fn test_role_constraints_validation_success() {
    let input = r#"
        topology ThresholdSig for Protocol {
            role_constraints {
                Witness: min = 3, max = 10
            }
        }
    "#;

    let parsed = Topology::parse(input).unwrap();
    let topology = parsed.topology;

    // Valid: exactly at minimum
    assert!(topology.validate_family("Witness", 3).is_ok());

    // Valid: in the middle
    assert!(topology.validate_family("Witness", 5).is_ok());

    // Valid: at maximum
    assert!(topology.validate_family("Witness", 10).is_ok());
}

#[test]
fn test_role_constraints_validation_failure() {
    let input = r#"
        topology ThresholdSig for Protocol {
            role_constraints {
                Witness: min = 3, max = 10
            }
        }
    "#;

    let parsed = Topology::parse(input).unwrap();
    let topology = parsed.topology;

    // Invalid: below minimum
    let err = topology.validate_family("Witness", 2).unwrap_err();
    assert!(err.to_string().contains("minimum"));

    // Invalid: above maximum
    let err = topology.validate_family("Witness", 11).unwrap_err();
    assert!(err.to_string().contains("maximum"));
}

#[test]
fn test_role_constraint_integration_with_adapter() {
    // Parse topology with constraints
    let input = r#"
        topology Prod for ThresholdSignature {
            role_constraints {
                Witness: min = 3, max = 10
            }
        }
    "#;
    let parsed = Topology::parse(input).unwrap();
    let topology = parsed.topology;

    // Create adapter with witnesses
    let adapter = TestAdapter::new(ThresholdRole::Coordinator).with_family(
        "Witness",
        vec![
            ThresholdRole::Witness(0),
            ThresholdRole::Witness(1),
            ThresholdRole::Witness(2),
            ThresholdRole::Witness(3),
            ThresholdRole::Witness(4),
        ],
    );

    // Resolve family and validate against topology
    let witnesses = adapter.resolve_family("Witness").unwrap();
    let validation = topology.validate_family("Witness", witnesses.len());
    assert!(
        validation.is_ok(),
        "5 witnesses should satisfy min=3, max=10"
    );
}

#[test]
fn test_role_constraint_fails_with_too_few() {
    let input = r#"
        topology Prod for ThresholdSignature {
            role_constraints {
                Witness: min = 5
            }
        }
    "#;
    let parsed = Topology::parse(input).unwrap();
    let topology = parsed.topology;

    // Create adapter with only 3 witnesses
    let adapter = TestAdapter::new(ThresholdRole::Coordinator).with_family(
        "Witness",
        vec![
            ThresholdRole::Witness(0),
            ThresholdRole::Witness(1),
            ThresholdRole::Witness(2),
        ],
    );

    let witnesses = adapter.resolve_family("Witness").unwrap();
    let validation = topology.validate_family("Witness", witnesses.len());
    assert!(
        validation.is_err(),
        "3 witnesses should fail min=5 constraint"
    );
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_resolve_family_not_found() {
    let adapter = TestAdapter::new(ThresholdRole::Coordinator);

    let result = adapter.resolve_family("Unknown");
    assert!(matches!(
        result,
        Err(ChoreographyError::RoleFamilyNotFound(_))
    ));
}

#[test]
fn test_resolve_range_invalid() {
    let adapter = TestAdapter::new(ThresholdRole::Coordinator).with_family(
        "Witness",
        vec![ThresholdRole::Witness(0), ThresholdRole::Witness(1)],
    );

    // Start > end is invalid
    let result = adapter.resolve_range("Witness", 5, 3);
    assert!(matches!(
        result,
        Err(ChoreographyError::InvalidRoleRange { .. })
    ));

    // Start beyond available is invalid
    let result = adapter.resolve_range("Witness", 10, 15);
    assert!(matches!(
        result,
        Err(ChoreographyError::InvalidRoleRange { .. })
    ));
}

#[test]
fn test_family_size() {
    let adapter = TestAdapter::new(ThresholdRole::Coordinator).with_family(
        "Witness",
        vec![
            ThresholdRole::Witness(0),
            ThresholdRole::Witness(1),
            ThresholdRole::Witness(2),
        ],
    );

    assert_eq!(adapter.family_size("Witness").unwrap(), 3);
    assert!(adapter.family_size("Unknown").is_err());
}

// ============================================================================
// Multi-Party Protocol Simulation
// ============================================================================

#[tokio::test]
async fn test_ring_broadcast_pattern() {
    // Test a ring topology where each node forwards to the next
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum RingRole {
        Node(u32),
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum RingLabel {
        Forward,
    }

    impl LabelId for RingLabel {
        fn as_str(&self) -> &'static str {
            "Forward"
        }

        fn from_str(label: &str) -> Option<Self> {
            if label == "Forward" {
                Some(RingLabel::Forward)
            } else {
                None
            }
        }
    }

    impl RoleId for RingRole {
        type Label = RingLabel;

        fn role_name(&self) -> RoleName {
            RoleName::from_static("Node")
        }

        fn role_index(&self) -> Option<u32> {
            match self {
                RingRole::Node(idx) => Some(*idx),
            }
        }
    }

    // Create a 5-node ring
    let nodes: Vec<RingRole> = (0..5).map(RingRole::Node).collect();
    let node0 = TestAdapter::new(RingRole::Node(0)).with_family("Node", nodes.clone());

    // Resolve all nodes
    let all_nodes = node0.resolve_family("Node").unwrap();
    assert_eq!(all_nodes.len(), 5);

    // Resolve subset [1, 4) - nodes 1, 2, 3
    let subset = node0.resolve_range("Node", 1, 4).unwrap();
    assert_eq!(subset.len(), 3);
    assert_eq!(subset[0], RingRole::Node(1));
    assert_eq!(subset[2], RingRole::Node(3));
}

// ============================================================================
// RoleFamilyConstraint Unit Tests
// ============================================================================

#[test]
fn test_role_family_constraint_defaults() {
    let constraint = RoleFamilyConstraint::default();
    assert_eq!(constraint.min, 0);
    assert_eq!(constraint.max, None);

    // Default allows any count
    assert!(constraint.validate(0).is_ok());
    assert!(constraint.validate(1000).is_ok());
}

#[test]
fn test_role_family_constraint_min_only() {
    let constraint = RoleFamilyConstraint::min_only(3);

    assert!(constraint.validate(2).is_err());
    assert!(constraint.validate(3).is_ok());
    assert!(constraint.validate(1000).is_ok());
}

#[test]
fn test_role_family_constraint_bounded() {
    let constraint = RoleFamilyConstraint::bounded(2, 5);

    assert!(constraint.validate(1).is_err());
    assert!(constraint.validate(2).is_ok());
    assert!(constraint.validate(5).is_ok());
    assert!(constraint.validate(6).is_err());
}
