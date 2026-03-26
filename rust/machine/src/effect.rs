//! Effect handler trait for the protocol machine guest-runtime boundary.
//!
//! The host runtime (simulator, application, integration harness, etc.)
//! implements this trait to provide material-specific behavior: computing
//! payloads for sends, processing received values, and performing integration
//! steps for a guest runtime that is driving the protocol machine.
//!
//! Normative integration contract:
//! - `topology_events` is queried once per scheduler round before pick/dispatch.
//! - external host events must enter through canonical ingress such as
//!   `handle_effect`, `topology_events`, `send_decision`, `handle_recv`,
//!   `step`, or `output_condition_hint`; embedders should not mutate
//!   session-local host state from ad hoc side channels during request
//!   handling.
//! - `send_decision` is the canonical send hook for `Send` and `Offer`.
//! - `handle_recv` is the canonical receive hook for `Receive` and `Choose`.
//! - `step` is called only from the `Invoke` instruction.
//! - `output_condition_hint` is queried only for eventful commits.
//! - `handle_send` and `handle_choose` are helper hooks for adapters and
//!   custom runners, not canonical session ingress surfaces.
//! - any host mutation of session-local runtime state should be routed through
//!   an explicit ownership capability such as `OwnedSession`.
//!
//! This is intentionally **not** the same as `telltale_runtime::ChoreoHandler`:
//! the protocol-machine guest-runtime handler is synchronous, session-local,
//! and operates on bytecode state, while `ChoreoHandler` is an async, typed
//! transport abstraction for generated choreography code.
//!
//! Integration guide: [`Effect Handlers and Session Types`](../../../docs/11_effect_session_bridge.md).

use crate::coroutine::Value;
use crate::output_condition::OutputConditionHint;
use crate::session::SessionId;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
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
