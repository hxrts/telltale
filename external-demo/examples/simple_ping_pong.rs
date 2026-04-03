//! Minimal downstream integration example using the current Telltale APIs.

use external_demo::{choreography, compile_choreography};
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use serde::{Deserialize, Serialize};
use std::error::Error;
use telltale::channel;

#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct Ping;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct Pong;

#[allow(dead_code)]
#[derive(telltale::Message)]
enum Label {
    Ping(Ping),
    Pong(Pong),
}

choreography! {
    protocol PingPong =
      roles Alice, Bob
      Alice -> Bob : Ping
      Bob -> Alice : Pong
}

const PING_PONG_DSL: &str = r#"
protocol PingPong =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
"#;

fn main() -> Result<(), Box<dyn Error>> {
    let compiled = compile_choreography(PING_PONG_DSL)?;
    let _roles = PingPong::sessions::setup();

    println!("protocol: {}", compiled.choreography.name);
    println!("roles: {:?}", compiled.role_names());
    println!("projected locals: {}", compiled.local_types.len());

    Ok(())
}
