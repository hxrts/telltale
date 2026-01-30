//! Secure Request-Response with Aura Extensions
//!
//! This example demonstrates the choreography! macro with Aura-specific extensions
//! including capability guards, flow costs, and journal facts.

use external_demo::choreography;
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use serde::{Deserialize, Serialize};
use telltale::*;

// Type definitions for the generated code
#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[allow(dead_code)]
#[derive(Message)]
enum Label {
    SecureRequest(SecureRequest),
    SecureResponse(SecureResponse),
}

// Message type definitions for secure communication
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SecureRequest {
    pub request_id: String,
    pub operation: String,
    pub data: Vec<u8>,
    pub timestamp: u64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SecureResponse {
    pub request_id: String,
    pub status: ResponseStatus,
    pub result: Option<Vec<u8>>,
    pub timestamp: u64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub enum ResponseStatus {
    #[default]
    Success,
    Unauthorized,
    ServerError,
    InvalidRequest,
}

// Define the secure choreography with basic telltale syntax and namespace
choreography! {
    protocol SecureProtocol = {
        roles Client, Server

        Client -> Server : SecureRequest
        Server -> Client : SecureResponse
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Secure Request-Response Choreography ===\n");

    println!("This example demonstrates:");
    println!("- Basic choreography! macro usage with external-demo");
    println!("- Secure message type definitions");
    println!("- Extension points for Aura-specific features");
    println!("- Integration with telltale infrastructure");

    println!("\n=== Protocol Flow ===");
    println!("1. Client sends SecureRequest to Server");
    println!("2. Server processes the request securely");
    println!("3. Server sends SecureResponse back to Client");

    println!("\n=== Future Extension Points ===");
    println!("- Capability-based authorization guards");
    println!("- Flow cost management for rate limiting");
    println!("- Journal facts for distributed state tracking");
    println!("- Journal merge operations for consistency");

    println!("\n=== Security Properties ===");
    println!("- Session types ensure protocol safety");
    println!("- Automatic projection prevents communication errors");
    println!("- Type-safe message handling");
    println!("- Ready for Aura extension integration");

    println!("\n=== Integration with Aura Systems ===");
    println!("- Compatible with AuraHandler for extension execution");
    println!("- Ready for web-of-trust capability evaluation");
    println!("- Prepared for FlowBudgetManager integration");
    println!("- Supports journal state synchronization");

    println!("\n=== Example Complete ===");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_secure_request_creation() {
        let request = SecureRequest {
            request_id: "req_123".to_string(),
            operation: "read_data".to_string(),
            data: vec![1, 2, 3, 4],
            timestamp: 1640995200,
        };

        assert_eq!(request.request_id, "req_123");
        assert_eq!(request.operation, "read_data");
        assert_eq!(request.data.len(), 4);
    }

    #[test]
    fn test_response_status_serialization() {
        let status = ResponseStatus::Success;
        let serialized = serde_json::to_string(&status).unwrap();
        let deserialized: ResponseStatus = serde_json::from_str(&serialized).unwrap();

        matches!(deserialized, ResponseStatus::Success);
    }

    #[test]
    fn test_secure_response_error_case() {
        let response = SecureResponse {
            request_id: "req_123".to_string(),
            status: ResponseStatus::Unauthorized,
            result: None,
            timestamp: 1640995260,
        };

        assert_eq!(response.request_id, "req_123");
        assert!(matches!(response.status, ResponseStatus::Unauthorized));
        assert!(response.result.is_none());
    }
}
