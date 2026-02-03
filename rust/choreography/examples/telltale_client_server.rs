#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Client-Server protocol example using TelltaleHandler
//
// This example demonstrates a simple request-response protocol between
// a client and server using Telltale's session-typed channels.

use serde::{Deserialize, Serialize};
use telltale_choreography::effects::{
    handlers::telltale::{SimpleChannel, TelltaleEndpoint, TelltaleHandler, TelltaleSession},
    ChoreoHandler, LabelId, RoleId,
};
use telltale_choreography::RoleName;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Role {
    Client,
    Server,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ClientServerLabel {
    Default,
}

impl LabelId for ClientServerLabel {
    fn as_str(&self) -> &'static str {
        match self {
            ClientServerLabel::Default => "default",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "default" => Some(ClientServerLabel::Default),
            _ => None,
        }
    }
}

impl RoleId for Role {
    type Label = ClientServerLabel;

    fn role_name(&self) -> RoleName {
        match self {
            Role::Client => RoleName::from_static("Client"),
            Role::Server => RoleName::from_static("Server"),
        }
    }
}

impl telltale::Role for Role {
    type Message = Message;

    fn seal(&mut self) {}
    fn is_sealed(&self) -> bool {
        false
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Message {
    Request(String),
    Response(String),
}

impl telltale::Message<Box<dyn std::any::Any + Send>> for Message {
    fn upcast(msg: Box<dyn std::any::Any + Send>) -> Self {
        *msg.downcast::<Message>().unwrap()
    }

    fn downcast(self) -> Result<Box<dyn std::any::Any + Send>, Self> {
        Ok(Box::new(self))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing
    tracing_subscriber::fmt::init();

    println!("=== Telltale Client-Server Example ===\n");

    // Create endpoints
    let mut client_ep = TelltaleEndpoint::new(Role::Client);
    let mut server_ep = TelltaleEndpoint::new(Role::Server);

    // Create bidirectional channels
    let (client_ch, server_ch) = SimpleChannel::pair();
    client_ep.register_session(
        Role::Server,
        TelltaleSession::from_simple_channel(client_ch),
    );
    server_ep.register_session(
        Role::Client,
        TelltaleSession::from_simple_channel(server_ch),
    );

    // Create handlers
    let mut client_handler = TelltaleHandler::<Role, Message>::new();
    let mut server_handler = TelltaleHandler::<Role, Message>::new();

    // Client sends request
    println!("Client: Sending request...");
    let request = Message::Request("Hello, Server!".to_string());
    client_handler
        .send(&mut client_ep, Role::Server, &request)
        .await?;

    // Server receives request
    let received_req: Message = server_handler.recv(&mut server_ep, Role::Client).await?;
    if let Message::Request(text) = received_req {
        println!("Server: Received request: {text}");

        // Server sends response
        println!("Server: Sending response...");
        let response = Message::Response(format!("Echo: {text}"));
        server_handler
            .send(&mut server_ep, Role::Client, &response)
            .await?;
    }

    // Client receives response
    let received_resp: Message = client_handler.recv(&mut client_ep, Role::Server).await?;
    if let Message::Response(text) = received_resp {
        println!("Client: Received response: {text}");
    }

    // Display session metadata
    println!("\n=== Session Metadata ===");
    println!("Client operations:");
    if let Some(meta) = client_ep.get_metadata(&Role::Server) {
        println!("  - Count: {}", meta.operation_count);
        println!("  - Last state: {}", meta.state_description);
    }

    println!("Server operations:");
    if let Some(meta) = server_ep.get_metadata(&Role::Client) {
        println!("  - Count: {}", meta.operation_count);
        println!("  - Last state: {}", meta.state_description);
    }

    // Cleanup
    client_ep.close_all_channels();
    server_ep.close_all_channels();

    println!("\n=== Protocol Complete ===");
    Ok(())
}
