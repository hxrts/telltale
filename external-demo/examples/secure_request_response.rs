//! Annotation-aware downstream integration example.

use external_demo::{choreography, compile_choreography, AnnotationScope};
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use serde::{Deserialize, Serialize};
use std::error::Error;
use telltale::channel;

#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct SecureRequest;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct Approved;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct Denied;

#[allow(dead_code)]
#[derive(telltale::Message)]
enum Label {
    SecureRequest(SecureRequest),
    Approved(Approved),
    Denied(Denied),
}

choreography! {
    protocol SecureProtocol =
      roles Client, Service
      Client { guard_capability : "auth:request", flow_cost : 10, leak : external } -> Service : SecureRequest
      choice Service at
        | Approve =>
          Service -> Client : Approved
        | Deny =>
          Service -> Client : Denied
}

const SECURE_PROTOCOL_DSL: &str = r#"
protocol SecureProtocol =
  roles Client, Service
  Client { guard_capability : "auth:request", flow_cost : 10, leak : external } -> Service : SecureRequest
  choice Service at
    | Approve =>
      Service -> Client : Approved
    | Deny =>
      Service -> Client : Denied
"#;

fn main() -> Result<(), Box<dyn Error>> {
    let compiled = compile_choreography(SECURE_PROTOCOL_DSL)?;
    let _roles = SecureProtocol::sessions::setup();

    let sender_annotations = compiled
        .annotation_records()
        .into_iter()
        .filter(|record| {
            record.path == "root"
                && record.scope == AnnotationScope::Sender
                && record.role.as_deref() == Some("Client")
        })
        .collect::<Vec<_>>();

    println!("roles: {:?}", compiled.role_names());
    println!(
        "ordered sender annotations: {:?}",
        sender_annotations
            .iter()
            .map(|record| format!("{}={}", record.key, record.value))
            .collect::<Vec<_>>()
    );
    println!("global json: {}", compiled.global_type_json()?);

    Ok(())
}
