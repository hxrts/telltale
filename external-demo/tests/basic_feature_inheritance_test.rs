//! Test suite verifying that external-demo inherits basic rumpsteak-aura features
//!
//! This test validates the core requirement: 3rd party projects should be able to
//! import rumpsteak-aura, get basic features, and use choreography! syntax.

use external_demo::choreography;
use external_demo::prelude::*;
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use rumpsteak_aura::channel;
use serde::{Deserialize, Serialize};

// Common type definitions needed for generated code
#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

// Message types for basic tests
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Message;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Request;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Response;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Data;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ImportRequest;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BasicFeatures;

#[allow(dead_code)]
#[derive(rumpsteak_aura::Message)]
enum Label {
    Message(Message),
    Request(Request),
    Response(Response),
    Data(Data),
    ImportRequest(ImportRequest),
    BasicFeatures(BasicFeatures),
}

#[test]
fn test_basic_choreography_inheritance() {
    // Test that basic choreography syntax works exactly like rumpsteak-aura
    choreography! {
        protocol BasicExample = {
            roles Alice, Bob
            Alice -> Bob : Message
        }
    }

    // If this compiles, basic feature inheritance is working
}

#[test]
fn test_simple_client_server() {
    // Test simple client-server protocol
    choreography! {
        protocol ClientServer = {
            roles Client, Server
            Client -> Server : Request
            Server -> Client : Response
        }
    }
}

#[test]
fn test_another_two_party_protocol() {
    // Test another two-party communication
    choreography! {
        protocol AnotherExample = {
            roles Sender, Receiver

            Sender -> Receiver : Data
        }
    }
}

/// Integration test that verifies the core requirement is met
#[test]
fn test_core_requirement_fulfilled() {
    // This test embodies the core requirement:
    // "3rd party developers can import rumpsteak-aura, get all features,
    //  and use choreography! macro syntax"

    // 1. Import rumpsteak-aura (✓ - via external_demo re-export)
    // 2. Get basic features (✓ - basic syntax works above)
    // 3. Use choreography! macro syntax (✓ - direct DSL syntax works)

    use rumpsteak_aura_choreography::compiler::{ExtensionParser, GrammarComposer};
    use rumpsteak_aura_choreography::extensions::ExtensionRegistry;

    // Verify extension system integration
    let _registry = ExtensionRegistry::new();
    let _composer = GrammarComposer::new();
    let _parser = ExtensionParser::new();

    // Verify choreography macro works with basic syntax
    choreography! {
        protocol RequirementValidation = {
            roles ThirdParty, RumpsteakAura

            // This validates that 3rd parties get basic functionality
            ThirdParty -> RumpsteakAura : ImportRequest
            RumpsteakAura -> ThirdParty : BasicFeatures
        }
    }

    // If this test compiles and runs, the core requirement is fulfilled ✓
}
