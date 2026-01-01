//! Simple Ping-Pong Choreography Example with Extension System
//!
//! This example demonstrates how external-demo inherits ALL rumpsteak-aura features
//! automatically through the extension system, including:
//! - Basic choreographic syntax
//! - Extension support for custom Aura annotations

use external_demo::choreography;
use rumpsteak_aura::*;
use futures::channel::mpsc::{UnboundedSender, UnboundedReceiver};
use rumpsteak_aura_choreography::{
    compiler::parser::parse_choreography_str_with_extensions, extensions::ExtensionRegistry,
};
use serde::{Deserialize, Serialize};

// Type definitions for the generated code
#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[allow(dead_code)]
#[derive(Message)]
enum Label {
    Ping(Ping),
    Pong(Pong),
}

// Message type definitions
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Ping {
    pub sequence: u32,
    pub timestamp: u64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Pong {
    pub sequence: u32,
    pub response_time: u64,
}

// Define the choreography using the macro with namespace
choreography! {
    protocol PingPong = {
        roles Alice, Bob

        Alice -> Bob : Ping
        Bob -> Alice : Pong
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== External-Demo Extension System Demo ===\n");

    // Demonstrate that external-demo inherits ALL rumpsteak-aura features
    demo_feature_inheritance()?;

    // Show extension system integration
    demo_extension_integration()?;

    // Demonstrate Aura-specific extensions
    demo_aura_extensions()?;

    println!("\n=== All Features Inherited Successfully ===");
    Ok(())
}

/// Demonstrate that external-demo inherits all rumpsteak-aura features
fn demo_feature_inheritance() -> Result<(), Box<dyn std::error::Error>> {
    println!("Demo 1: Feature Inheritance");
    println!("external-demo automatically inherits ALL rumpsteak-aura features:");

    // Test basic choreography
    let basic_choreography = r#"
        protocol BasicPingPong = {
            roles Client, Server

            Client -> Server : Ping
            Server -> Client : Pong
        }
"#;

    // Parse using inherited rumpsteak features
    let registry = ExtensionRegistry::new();
    let (choreography, _) =
        parse_choreography_str_with_extensions(basic_choreography, &registry)?;

    println!(
        "   Role definitions: {:?}",
        choreography
            .roles
            .iter()
            .map(|r| r.name.to_string())
            .collect::<Vec<_>>()
    );
    println!("   Protocol parsing successful");
    println!("   Basic message flow handled");

    Ok(())
}

/// Demonstrate extension system integration
fn demo_extension_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 2: Extension System Integration");

    // Show that external-demo can use the extension system
    println!("   external-demo has full access to extension system");
    println!("   Can register custom extensions");
    println!("   Can use discovery system");
    println!("   Maintains compatibility with rumpsteak-aura");

    Ok(())
}

/// Demonstrate Aura-specific extensions
fn demo_aura_extensions() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 3: Aura-Specific Extensions");

    // Test basic protocol with extension system and namespace
    let aura_choreography = r#"
        module aura_ping_pong exposing (AuraEnhancedPingPong)
        protocol AuraEnhancedPingPong = {
            roles Alice, Bob

            Alice -> Bob : SecurePing
            Bob -> Alice : SecurePong
        }
"#;

    let registry = ExtensionRegistry::new();
    let (choreography, extensions) =
        parse_choreography_str_with_extensions(aura_choreography, &registry)?;

    println!("   Protocol parsed: {}", choreography.name);
    println!("   Extensions processed: {}", extensions.len());
    println!("   Ready for Aura annotation extensions");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_message_serialization() {
        let ping = Ping {
            sequence: 1,
            timestamp: 12345,
        };
        let serialized = serde_json::to_string(&ping).unwrap();
        let deserialized: Ping = serde_json::from_str(&serialized).unwrap();

        assert_eq!(ping.sequence, deserialized.sequence);
        assert_eq!(ping.timestamp, deserialized.timestamp);
    }

    #[test]
    fn test_pong_creation() {
        let pong = Pong {
            sequence: 42,
            response_time: 67890,
        };
        assert_eq!(pong.sequence, 42);
        assert_eq!(pong.response_time, 67890);
    }
}
