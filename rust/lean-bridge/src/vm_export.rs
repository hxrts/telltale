//! VM-state export helpers for Lean bridge JSON payloads.
//!
//! This module is intentionally generic and does not depend on `telltale-vm`
//! to avoid cross-crate cycles. Runtime adapters can map concrete VM state
//! into these export structs before serialization.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value as Json};

/// Schema version for VM-state export payloads.
pub const VM_STATE_SCHEMA_VERSION: &str = "vm_state.v1";

#[must_use]
pub fn default_vm_state_schema_version() -> String {
    VM_STATE_SCHEMA_VERSION.to_string()
}

/// Compatibility metadata included in exported payloads.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct CompatibilityMeta {
    /// Schema family identifier.
    pub family: String,
    /// Current schema version.
    pub version: String,
    /// Backward-compatible schema versions accepted by this exporter.
    pub backward_compatible_from: Vec<String>,
}

impl Default for CompatibilityMeta {
    fn default() -> Self {
        Self {
            family: "vm_state".to_string(),
            version: VM_STATE_SCHEMA_VERSION.to_string(),
            backward_compatible_from: vec!["vm_state.v0".to_string()],
        }
    }
}

/// Endpoint reference in exported VM-state payloads.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct EndpointRef {
    pub sid: usize,
    pub role: String,
}

/// Session view in exported VM-state payloads.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct SessionView {
    pub sid: usize,
    pub roles: Vec<String>,
    pub status: String,
    pub epoch: usize,
}

/// Generic exported coroutine state.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(bound(deserialize = "G: Deserialize<'de>, E: Deserialize<'de>"))]
pub struct CoroutineState<G, E> {
    pub id: usize,
    #[serde(rename = "programId", alias = "program_id")]
    pub program_id: usize,
    pub pc: usize,
    pub status: G,
    #[serde(rename = "ownedEndpoints", alias = "owned_endpoints")]
    pub owned_endpoints: Vec<EndpointRef>,
    #[serde(rename = "costBudget", alias = "cost_budget")]
    pub cost_budget: usize,
    #[serde(rename = "effectCtx", alias = "effect_ctx")]
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub effect_ctx: Option<E>,
}

/// Ticked observable event wrapper used in exports.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(bound(deserialize = "E: Deserialize<'de>"))]
pub struct TickedObsEvent<E> {
    pub tick: u64,
    pub event: E,
}

/// Generic exported VM state.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(bound(deserialize = "G: Deserialize<'de>, E: Deserialize<'de>"))]
pub struct VMState<G, E> {
    #[serde(default = "default_vm_state_schema_version")]
    pub schema_version: String,
    #[serde(default)]
    pub compatibility: CompatibilityMeta,
    pub clock: u64,
    #[serde(rename = "nextCoroId", alias = "next_coro_id")]
    pub next_coro_id: usize,
    #[serde(rename = "nextSessionId", alias = "next_session_id")]
    pub next_session_id: usize,
    pub coroutines: Vec<CoroutineState<G, E>>,
    pub sessions: Vec<SessionView>,
    #[serde(rename = "obsTrace", alias = "obs_trace")]
    pub obs_trace: Vec<TickedObsEvent<E>>,
}

/// Convert a full VM-state payload to canonical JSON.
#[must_use]
pub fn vm_state_to_json<G, E>(vm: &VMState<G, E>) -> Json
where
    G: Serialize,
    E: Serialize,
{
    json!({
        "schema_version": VM_STATE_SCHEMA_VERSION,
        "compatibility": vm.compatibility,
        "clock": vm.clock,
        "nextCoroId": vm.next_coro_id,
        "nextSessionId": vm.next_session_id,
        "coroutines": vm.coroutines.iter().map(coroutine_to_json).collect::<Vec<_>>(),
        "sessions": sessions_to_json(&vm.sessions),
        "obsTrace": vm.obs_trace.iter().map(event_to_json).collect::<Vec<_>>(),
    })
}

/// Decode a VM-state payload from JSON with compatibility aliases.
pub fn vm_state_from_json<G, E>(value: Json) -> Result<VMState<G, E>, serde_json::Error>
where
    G: for<'de> Deserialize<'de>,
    E: for<'de> Deserialize<'de>,
{
    serde_json::from_value(value)
}

/// Convert one coroutine payload to JSON.
#[must_use]
pub fn coroutine_to_json<G, E>(coro: &CoroutineState<G, E>) -> Json
where
    G: Serialize,
    E: Serialize,
{
    json!({
        "id": coro.id,
        "programId": coro.program_id,
        "pc": coro.pc,
        "status": status_to_json(&coro.status),
        "ownedEndpoints": coro.owned_endpoints.iter().map(endpoint_to_json).collect::<Vec<_>>(),
        "costBudget": coro.cost_budget,
        "effectCtx": coro.effect_ctx.as_ref().map_or(Json::Null, |ctx| serde_json::to_value(ctx).unwrap_or(Json::Null)),
    })
}

/// Convert one ticked event payload to JSON.
#[must_use]
pub fn event_to_json<E>(event: &TickedObsEvent<E>) -> Json
where
    E: Serialize,
{
    json!({
        "schema_version": VM_STATE_SCHEMA_VERSION,
        "tick": event.tick,
        "event": obs_event_to_json(&event.event),
    })
}

/// Convert coroutine status to JSON.
#[must_use]
pub fn status_to_json<S>(status: &S) -> Json
where
    S: Serialize,
{
    serde_json::to_value(status).unwrap_or(Json::Null)
}

/// Convert session views to JSON.
#[must_use]
pub fn sessions_to_json(sessions: &[SessionView]) -> Json {
    Json::Array(
        sessions
            .iter()
            .map(|s| {
                json!({
                    "sid": s.sid,
                    "roles": s.roles,
                    "status": s.status,
                    "epoch": s.epoch,
                })
            })
            .collect(),
    )
}

/// Convert endpoint reference to JSON.
#[must_use]
pub fn endpoint_to_json(endpoint: &EndpointRef) -> Json {
    json!({
        "sid": endpoint.sid,
        "role": endpoint.role,
    })
}

/// Convert one observable event payload to JSON.
#[must_use]
pub fn obs_event_to_json<E>(event: &E) -> Json
where
    E: Serialize,
{
    serde_json::to_value(event).unwrap_or(Json::Null)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
    struct Status {
        kind: String,
    }

    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
    struct Event {
        kind: String,
        label: String,
    }

    #[test]
    fn vm_export_includes_schema_and_compatibility() {
        let vm = VMState {
            schema_version: default_vm_state_schema_version(),
            compatibility: CompatibilityMeta::default(),
            clock: 7,
            next_coro_id: 3,
            next_session_id: 2,
            coroutines: vec![CoroutineState {
                id: 0,
                program_id: 1,
                pc: 4,
                status: Status {
                    kind: "ready".to_string(),
                },
                owned_endpoints: vec![EndpointRef {
                    sid: 1,
                    role: "A".to_string(),
                }],
                cost_budget: 100,
                effect_ctx: Some(Event {
                    kind: "ctx".to_string(),
                    label: "ok".to_string(),
                }),
            }],
            sessions: vec![SessionView {
                sid: 1,
                roles: vec!["A".to_string(), "B".to_string()],
                status: "active".to_string(),
                epoch: 0,
            }],
            obs_trace: vec![TickedObsEvent {
                tick: 7,
                event: Event {
                    kind: "sent".to_string(),
                    label: "msg".to_string(),
                },
            }],
        };

        let json = vm_state_to_json(&vm);
        assert_eq!(json["schema_version"], VM_STATE_SCHEMA_VERSION);
        assert_eq!(json["compatibility"]["family"], "vm_state");
        assert_eq!(json["nextCoroId"], 3);
        assert_eq!(json["nextSessionId"], 2);
        assert_eq!(json["coroutines"][0]["ownedEndpoints"][0]["sid"], 1);
        assert_eq!(json["obsTrace"][0]["tick"], 7);
    }

    #[test]
    fn vm_export_roundtrip_via_json_decoder() {
        let vm = VMState {
            schema_version: default_vm_state_schema_version(),
            compatibility: CompatibilityMeta::default(),
            clock: 9,
            next_coro_id: 5,
            next_session_id: 4,
            coroutines: vec![CoroutineState {
                id: 1,
                program_id: 2,
                pc: 3,
                status: Status {
                    kind: "blocked".to_string(),
                },
                owned_endpoints: vec![EndpointRef {
                    sid: 1,
                    role: "A".to_string(),
                }],
                cost_budget: 44,
                effect_ctx: None::<Event>,
            }],
            sessions: vec![SessionView {
                sid: 1,
                roles: vec!["A".to_string(), "B".to_string()],
                status: "active".to_string(),
                epoch: 2,
            }],
            obs_trace: vec![TickedObsEvent {
                tick: 0,
                event: Event {
                    kind: "sent".to_string(),
                    label: "msg".to_string(),
                },
            }],
        };

        let encoded = vm_state_to_json(&vm);
        let decoded: VMState<Status, Event> = vm_state_from_json(encoded).expect("decode vm state");
        assert_eq!(decoded.schema_version, VM_STATE_SCHEMA_VERSION);
        assert_eq!(decoded.next_coro_id, 5);
        assert_eq!(decoded.coroutines[0].program_id, 2);
        assert_eq!(decoded.obs_trace[0].tick, 0);
    }

    #[test]
    fn vm_export_legacy_aliases_decode() {
        let legacy = json!({
            "schema_version": "vm_state.v0",
            "clock": 1,
            "next_coro_id": 7,
            "next_session_id": 3,
            "coroutines": [{
                "id": 0,
                "program_id": 4,
                "pc": 0,
                "status": {"kind": "ready"},
                "owned_endpoints": [{"sid": 1, "role": "A"}],
                "cost_budget": 99,
                "effect_ctx": null
            }],
            "sessions": [{
                "sid": 1,
                "roles": ["A", "B"],
                "status": "active",
                "epoch": 0
            }],
            "obs_trace": [{
                "tick": 1,
                "event": {"kind": "sent", "label": "msg"}
            }]
        });

        let decoded: VMState<Status, Event> =
            vm_state_from_json(legacy).expect("decode legacy vm state");
        assert_eq!(decoded.schema_version, "vm_state.v0");
        assert_eq!(decoded.next_coro_id, 7);
        assert_eq!(decoded.coroutines[0].program_id, 4);
        assert_eq!(decoded.obs_trace.len(), 1);
    }
}
