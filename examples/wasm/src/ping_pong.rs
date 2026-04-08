//! WASM example: canonical `tell!`-based ping-pong protocol.
//!
//! This is an effect-boundary example for browser integration: `tell!` owns the
//! ping-pong protocol, and a generated effect trait models the host-side logic
//! that turns a received ping into a pong payload.

use futures::try_join;
use serde::{Deserialize, Serialize};
use telltale::{tell, try_session};
use wasm_bindgen::prelude::*;

tell! {
    -- // Execution profile keeps the example on the proof-backed effect boundary.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Browser host transforms the received ping into a pong payload.
    effect BrowserRuntime
      command respond : String -> String
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Alice sends a ping and Bob replies with a pong.
    protocol PingPong uses BrowserRuntime under Replay =
      roles Alice, Bob
      Alice -> Bob : Ping of String
      Bob -> Alice : Pong of String
}

use PingPong::effects;
use PingPong::sessions::*;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PingPongResult {
    pub sent_ping: String,
    pub received_ping: String,
    pub sent_pong: String,
    pub received_pong: String,
}

#[derive(Default)]
struct BrowserHost;

impl effects::BrowserRuntime for BrowserHost {
    fn respond(&mut self, input: String) -> String {
        format!("Pong for: {input}")
    }
}

async fn alice(role: &mut Alice, message: String) -> Result<String, JsValue> {
    try_session(role, |s: AliceSession<'_, _>| async move {
        let s = s.send(Ping(message)).await.map_err(to_js_error)?;
        let (Pong(response), s) = s.receive().await.map_err(to_js_error)?;
        Ok((response, s))
    })
    .await
}

async fn bob(role: &mut Bob, host: &mut BrowserHost) -> Result<(String, String), JsValue> {
    try_session(role, |s: BobSession<'_, _>| async move {
        let (Ping(received_ping), s) = s.receive().await.map_err(to_js_error)?;
        let sent_pong = effects::BrowserRuntime::respond(host, received_ping.clone());
        let s = s.send(Pong(sent_pong.clone())).await.map_err(to_js_error)?;
        Ok(((received_ping, sent_pong), s))
    })
    .await
}

fn to_js_error<E: std::fmt::Display>(error: E) -> JsValue {
    JsValue::from_str(&format!("Protocol error: {error}"))
}

#[wasm_bindgen(start)]
pub fn init() {
    console_error_panic_hook::set_once();
    let _ = tracing_wasm::try_set_as_global_default();
}

#[wasm_bindgen]
pub async fn run_ping_pong(message: String) -> Result<JsValue, JsValue> {
    let Roles(mut alice_role, mut bob_role) = Roles::default();
    let sent_ping = message.clone();
    let mut browser_host = BrowserHost;

    let (received_pong, (received_ping, sent_pong)) = try_join!(
        alice(&mut alice_role, message),
        bob(&mut bob_role, &mut browser_host)
    )?;

    serde_wasm_bindgen::to_value(&PingPongResult {
        sent_ping,
        received_ping,
        sent_pong,
        received_pong,
    })
    .map_err(|error| JsValue::from_str(&format!("Serialization error: {error}")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;

    wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    fn generated_protocol_surface_exists() {
        let _roles = Roles::default();
    }

    #[wasm_bindgen_test(async)]
    async fn ping_pong_round_trip_succeeds() {
        init();

        let value = match run_ping_pong("Hello from Alice!".to_string()).await {
            Ok(value) => value,
            Err(error) => panic!("protocol should succeed: {error:?}"),
        };
        let result: PingPongResult = match serde_wasm_bindgen::from_value(value) {
            Ok(result) => result,
            Err(error) => panic!("result should deserialize: {error}"),
        };

        assert_eq!(result.sent_ping, "Hello from Alice!");
        assert_eq!(result.received_ping, "Hello from Alice!");
        assert_eq!(result.sent_pong, "Pong for: Hello from Alice!");
        assert_eq!(result.received_pong, "Pong for: Hello from Alice!");
    }
}
