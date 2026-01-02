// WASM example: Simple ping-pong protocol
//
// Demonstrates how to use Rumpsteak choreographic programming in WASM.
// This is a minimal two-party protocol where Alice sends a ping and Bob responds with a pong.

use wasm_bindgen::prelude::*;
use rumpsteak_aura_choreography::{
    InMemoryHandler, Program, interpret, RoleId, LabelId, RoleName,
};
use serde::{Serialize, Deserialize};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

/// Initialize panic hook for better error messages in browser console
#[wasm_bindgen(start)]
pub fn init() {
    console_error_panic_hook::set_once();
    tracing_wasm::set_as_global_default();
}

/// Role definitions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Role {
    Alice,
    Bob,
}

/// Label definitions for choice branches
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Label {
    Ping,
    Pong,
}

impl LabelId for Label {
    fn as_str(&self) -> &'static str {
        match self {
            Label::Ping => "Ping",
            Label::Pong => "Pong",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "Ping" => Some(Label::Ping),
            "Pong" => Some(Label::Pong),
            _ => None,
        }
    }
}

impl RoleId for Role {
    type Label = Label;

    fn role_name(&self) -> RoleName {
        match self {
            Role::Alice => RoleName::from_static("Alice"),
            Role::Bob => RoleName::from_static("Bob"),
        }
    }
}

/// Message types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Message {
    Ping(String),
    Pong(String),
}

/// Run the ping-pong protocol from Alice's perspective
#[wasm_bindgen]
pub async fn run_alice(message: String) -> Result<String, JsValue> {
    tracing::info!("Alice: Starting ping-pong protocol");
    
    // Create shared channels for communication
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));
    
    // Create handler for Alice
    let mut handler = InMemoryHandler::with_channels(
        Role::Alice,
        channels.clone(),
        choice_channels.clone(),
    );
    
    // Define Alice's protocol: send ping to Bob
    let program = Program::new()
        .send(Role::Bob, Message::Ping(message.clone()))
        .recv::<Message>(Role::Bob)
        .end();
    
    // Execute protocol
    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .map_err(|e| JsValue::from_str(&format!("Protocol error: {:?}", e)))?;
    
    // Extract received message
    if let Some(Message::Pong(response)) = result.received_values.first() {
        Ok(response.clone())
    } else {
        Err(JsValue::from_str("Did not receive expected Pong message"))
    }
}

/// Run the ping-pong protocol from Bob's perspective
#[wasm_bindgen]
pub async fn run_bob() -> Result<String, JsValue> {
    tracing::info!("Bob: Starting ping-pong protocol");
    
    // Create shared channels for communication
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));
    
    // Create handler for Bob
    let mut handler = InMemoryHandler::with_channels(
        Role::Bob,
        channels.clone(),
        choice_channels.clone(),
    );
    
    // Define Bob's protocol: receive ping from Alice, respond with pong
    let program = Program::new()
        .recv::<Message>(Role::Alice)
        .send(Role::Alice, Message::Pong("Hello from Bob!".to_string()))
        .end();
    
    // Execute protocol
    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .map_err(|e| JsValue::from_str(&format!("Protocol error: {:?}", e)))?;
    
    // Extract received message
    if let Some(Message::Ping(ping_msg)) = result.received_values.first() {
        Ok(ping_msg.clone())
    } else {
        Err(JsValue::from_str("Did not receive expected Ping message"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;
    
    wasm_bindgen_test_configure!(run_in_browser);
    
    #[wasm_bindgen_test]
    fn test_role_creation() {
        init();
        
        // Test role enum creation
        let alice = Role::Alice;
        let bob = Role::Bob;
        
        // Roles can be compared
        assert_ne!(alice, bob);
        assert_eq!(alice, Role::Alice);
    }
    
    #[wasm_bindgen_test]
    fn test_message_serialization() {
        init();
        
        // Test that messages can be created
        let ping = Message::Ping("test".to_string());
        let pong = Message::Pong("response".to_string());
        
        // Verify message enum variants work
        match ping {
            Message::Ping(s) => assert_eq!(s, "test"),
            _ => panic!("Expected Ping variant"),
        }
        
        match pong {
            Message::Pong(s) => assert_eq!(s, "response"),
            _ => panic!("Expected Pong variant"),
        }
    }
    
    #[wasm_bindgen_test]
    fn test_handler_creation() {
        init();
        
        // Test that handlers can be created with shared channels
        let channels = Arc::new(Mutex::new(HashMap::new()));
        let choice_channels = Arc::new(Mutex::new(HashMap::new()));
        
        let alice = InMemoryHandler::with_channels(
            Role::Alice,
            channels.clone(),
            choice_channels.clone(),
        );
        
        let bob = InMemoryHandler::with_channels(
            Role::Bob,
            channels.clone(),
            choice_channels.clone(),
        );
        
        // Test passes if handlers can be created without panicking
        drop(alice);
        drop(bob);
    }
    
    #[wasm_bindgen_test]
    async fn test_program_creation() {
        init();
        
        // Test that effect programs can be created
        let _alice_program = Program::new()
            .send(Role::Bob, Message::Ping("test".to_string()))
            .recv::<Message>(Role::Bob)
            .end();
        
        let _bob_program = Program::new()
            .recv::<Message>(Role::Alice)
            .send(Role::Alice, Message::Pong("response".to_string()))
            .end();
        
        // Test passes if programs compile and can be created
    }
}

