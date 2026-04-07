//! Typed persisted replay artifacts for simulator checkpoints and replayable runs.

use std::path::Path;

use serde::{Deserialize, Serialize};
use telltale_machine::ProtocolMachine;

use crate::execution::ScenarioMiddlewareCheckpoint;
use crate::runner::ScenarioReplayArtifact;

/// Stable schema version for persisted simulator replay artifacts.
pub const PERSISTED_REPLAY_SCHEMA_VERSION: &str = "telltale.simulator.persisted_replay.v1";

/// One serialized canonical checkpoint emitted during scenario execution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckpointArtifact {
    /// Tick at which the checkpoint was captured.
    pub tick: u64,
    /// Serialized protocol-machine state payload.
    pub machine_state: Vec<u8>,
    /// Exact middleware state needed for semantics-preserving resume.
    pub(crate) middleware_state: Option<ScenarioMiddlewareCheckpoint>,
}

impl PartialEq for CheckpointArtifact {
    fn eq(&self, other: &Self) -> bool {
        self.tick == other.tick && self.machine_state == other.machine_state
    }
}

impl Eq for CheckpointArtifact {}

impl CheckpointArtifact {
    /// Build one checkpoint artifact from a machine snapshot and middleware state.
    ///
    /// # Errors
    ///
    /// Returns an error when the machine cannot be serialized.
    pub(crate) fn capture(
        tick: u64,
        machine: &ProtocolMachine,
        middleware_state: Option<ScenarioMiddlewareCheckpoint>,
    ) -> Result<Self, String> {
        let machine_state = serde_cbor::to_vec(machine)
            .map_err(|err| format!("failed to serialize checkpoint {tick}: {err}"))?;
        Ok(Self {
            tick,
            machine_state,
            middleware_state,
        })
    }

    /// Decode the serialized protocol-machine state.
    ///
    /// # Errors
    ///
    /// Returns an error when the serialized checkpoint payload is invalid.
    pub fn decode_machine(&self) -> Result<ProtocolMachine, String> {
        serde_cbor::from_slice(&self.machine_state)
            .map_err(|err| format!("decode checkpoint artifact: {err}"))
    }

    /// Convert the checkpoint into the persisted replay wrapper format.
    #[must_use]
    pub fn into_persisted(self) -> PersistedReplayArtifact {
        PersistedReplayArtifact::checkpoint(self)
    }
}

/// Kind-tagged persisted replay payload.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "kind", content = "payload")]
pub enum PersistedReplayPayload {
    /// Exact checkpoint-resume artifact with middleware state.
    Checkpoint(Box<CheckpointArtifact>),
    /// Replay-visible run artifact emitted by one completed scenario run.
    ScenarioReplay(Box<ScenarioReplayArtifact>),
}

/// Typed persisted replay wrapper for simulator checkpoints and replayable runs.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct PersistedReplayArtifact {
    /// Stable schema version for this persisted artifact family.
    pub schema_version: String,
    /// Concrete persisted payload.
    pub payload: PersistedReplayPayload,
}

impl PersistedReplayArtifact {
    /// Wrap one checkpoint artifact for persistence.
    #[must_use]
    pub fn checkpoint(checkpoint: CheckpointArtifact) -> Self {
        Self {
            schema_version: PERSISTED_REPLAY_SCHEMA_VERSION.to_string(),
            payload: PersistedReplayPayload::Checkpoint(Box::new(checkpoint)),
        }
    }

    /// Wrap one completed run replay artifact for persistence.
    #[must_use]
    pub fn scenario_replay(replay: ScenarioReplayArtifact) -> Self {
        Self {
            schema_version: PERSISTED_REPLAY_SCHEMA_VERSION.to_string(),
            payload: PersistedReplayPayload::ScenarioReplay(Box::new(replay)),
        }
    }

    /// Decode one persisted replay artifact from CBOR bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are invalid CBOR, the schema version is unknown,
    /// or the payload does not decode.
    pub fn from_slice(bytes: &[u8]) -> Result<Self, String> {
        let artifact: Self = serde_cbor::from_slice(bytes)
            .map_err(|err| format!("decode persisted replay artifact: {err}"))?;
        if artifact.schema_version != PERSISTED_REPLAY_SCHEMA_VERSION {
            return Err(format!(
                "unsupported persisted replay schema version `{}`",
                artifact.schema_version
            ));
        }
        Ok(artifact)
    }

    /// Load one persisted replay artifact from disk.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or the artifact cannot be decoded.
    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = path.as_ref();
        let bytes = std::fs::read(path)
            .map_err(|err| format!("read persisted replay artifact {}: {err}", path.display()))?;
        Self::from_slice(&bytes)
    }

    /// Encode the artifact as CBOR bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if serialization fails.
    pub fn to_cbor(&self) -> Result<Vec<u8>, String> {
        serde_cbor::to_vec(self).map_err(|err| format!("encode persisted replay artifact: {err}"))
    }

    /// Persist the artifact to disk as CBOR.
    ///
    /// # Errors
    ///
    /// Returns an error if serialization or file writing fails.
    pub fn write_to_path(&self, path: impl AsRef<Path>) -> Result<(), String> {
        let path = path.as_ref();
        let bytes = self.to_cbor()?;
        std::fs::write(path, bytes)
            .map_err(|err| format!("write persisted replay artifact {}: {err}", path.display()))
    }

    /// Borrow the checkpoint payload when this artifact wraps one.
    #[must_use]
    pub fn checkpoint_artifact(&self) -> Option<&CheckpointArtifact> {
        match &self.payload {
            PersistedReplayPayload::Checkpoint(checkpoint) => Some(checkpoint.as_ref()),
            PersistedReplayPayload::ScenarioReplay(_) => None,
        }
    }

    /// Consume the wrapper into one checkpoint artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if this persisted artifact is not a checkpoint payload.
    pub fn into_checkpoint_artifact(self) -> Result<CheckpointArtifact, String> {
        match self.payload {
            PersistedReplayPayload::Checkpoint(checkpoint) => Ok(*checkpoint),
            PersistedReplayPayload::ScenarioReplay(_) => Err(
                "persisted replay artifact contains a scenario replay payload, not a checkpoint"
                    .to_string(),
            ),
        }
    }
}
