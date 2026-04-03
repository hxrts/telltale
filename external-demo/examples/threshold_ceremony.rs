//! Namespaced protocol compilation example.

use external_demo::{choreography, compile_choreography};
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use serde::{Deserialize, Serialize};
use std::error::Error;
use telltale::channel;

#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct Start;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct Commitment;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct FinalSignature;

#[allow(dead_code)]
#[derive(telltale::Message)]
enum Label {
    Start(Start),
    Commitment(Commitment),
    FinalSignature(FinalSignature),
}

choreography! {
    module threshold exposing (ThresholdCeremony)

    protocol ThresholdCeremony =
      roles Coordinator, SignerA, SignerB
      Coordinator -> SignerA : Start
      Coordinator -> SignerB : Start
      SignerA -> Coordinator : Commitment
      SignerB -> Coordinator : Commitment
      Coordinator -> SignerA : FinalSignature
      Coordinator -> SignerB : FinalSignature
}

const THRESHOLD_CEREMONY_DSL: &str = r#"
module threshold exposing (ThresholdCeremony)

protocol ThresholdCeremony =
  roles Coordinator, SignerA, SignerB
  Coordinator -> SignerA : Start
  Coordinator -> SignerB : Start
  SignerA -> Coordinator : Commitment
  SignerB -> Coordinator : Commitment
  Coordinator -> SignerA : FinalSignature
  Coordinator -> SignerB : FinalSignature
"#;

fn main() -> Result<(), Box<dyn Error>> {
    let compiled = compile_choreography(THRESHOLD_CEREMONY_DSL)?;
    let _roles = threshold::ThresholdCeremony::sessions::setup();

    println!("protocol: {}", compiled.choreography.name);
    println!("role order: {:?}", compiled.role_names());
    println!("global json: {}", compiled.global_type_json()?);
    println!("local json: {}", compiled.local_type_r_json()?);

    Ok(())
}
