//! Guard-layer typed interface.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::coroutine::Value;

/// Guard-layer identifier.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct LayerId(pub String);

impl From<&str> for LayerId {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

/// Lean-style guard layer API.
pub trait GuardLayer {
    /// Guard resource type.
    type Resource: Clone;
    /// Evidence type produced/consumed by acquire/release.
    type Evidence: Clone;

    /// Acquire a layer resource and produce evidence.
    fn open_(&mut self, layer: &LayerId) -> Result<(Self::Resource, Self::Evidence), String>;
    /// Release a layer resource and consume evidence.
    fn close(&mut self, layer: &LayerId, evidence: Self::Evidence) -> Result<(), String>;
    /// Encode evidence for register transport.
    fn encode_evidence(evidence: &Self::Evidence) -> Result<Value, String>;
    /// Decode evidence from register value.
    fn decode_evidence(value: &Value) -> Result<Self::Evidence, String>;

    /// Lean-name compatibility wrapper.
    #[allow(non_snake_case)]
    fn encodeEvidence(evidence: &Self::Evidence) -> Result<Value, String> {
        Self::encode_evidence(evidence)
    }

    /// Lean-name compatibility wrapper.
    #[allow(non_snake_case)]
    fn decodeEvidence(value: &Value) -> Result<Self::Evidence, String> {
        Self::decode_evidence(value)
    }
}

/// Basic in-memory guard layer.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct InMemoryGuardLayer {
    /// Available resources by layer id.
    pub resources: BTreeMap<LayerId, Value>,
}

impl GuardLayer for InMemoryGuardLayer {
    type Resource = Value;
    type Evidence = Value;

    fn open_(&mut self, layer: &LayerId) -> Result<(Self::Resource, Self::Evidence), String> {
        let resource = self
            .resources
            .get(layer)
            .cloned()
            .ok_or_else(|| format!("unknown guard layer {}", layer.0))?;
        Ok((resource.clone(), resource))
    }

    fn close(&mut self, layer: &LayerId, evidence: Self::Evidence) -> Result<(), String> {
        if !self.resources.contains_key(layer) {
            return Err(format!("unknown guard layer {}", layer.0));
        }
        let _ = evidence;
        Ok(())
    }

    fn encode_evidence(evidence: &Self::Evidence) -> Result<Value, String> {
        Ok(evidence.clone())
    }

    fn decode_evidence(value: &Value) -> Result<Self::Evidence, String> {
        Ok(value.clone())
    }
}
