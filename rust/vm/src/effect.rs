//! Effect handler trait for the VM.
//!
//! The host (simulator, application, etc.) implements this trait to provide
//! material-specific behavior: computing payloads for sends, processing
//! received values, and performing integration steps.
//!
//! Normative integration contract:
//! - `topology_events` is queried once per scheduler round before pick/dispatch.
//! - `send_decision` is the canonical send hook for `Send` and `Offer`.
//! - `handle_recv` is the canonical receive hook for `Receive` and `Choose`.
//! - `step` is called only from the `Invoke` instruction.
//! - `output_condition_hint` is queried only for eventful commits.
//! - `handle_send` and `handle_choose` are compatibility hooks.
//!
//! This is intentionally **not** the same as `telltale_choreography::ChoreoHandler`:
//! the VM handler is synchronous, session-local, and operates on bytecode state,
//! while `ChoreoHandler` is an async, typed transport abstraction for generated
//! choreography code.
//!
//! Integration guide: [`Effect Handlers and Session Types`](../../../docs/11_effect_session_bridge.md).

use crate::coroutine::Value;
use crate::output_condition::OutputConditionHint;
use crate::session::SessionId;
use serde::{Deserialize, Serialize};
use serde_json::json;
use serde_json::Value as JsonValue;
use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

include!("effect/core_types.rs");
include!("effect/runtime_types.rs");
include!("effect/handler_trait.rs");
include!("effect/recording_impl.rs");
include!("effect/replay_impl.rs");
