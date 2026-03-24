//! ProtocolMachine state checkpoints for replay and debugging.

use std::collections::BTreeMap;
use std::path::PathBuf;

use telltale_protocol_machine::ProtocolMachine;

/// Serialized ProtocolMachine state blob.
pub type SerializedState = Vec<u8>;

/// Periodic ProtocolMachine state snapshots for replay and debugging.
pub struct CheckpointStore {
    checkpoints: BTreeMap<u64, SerializedState>,
    interval: u64,
    dir: Option<PathBuf>,
    last_persist_error: Option<String>,
}

impl CheckpointStore {
    /// Create a new checkpoint store.
    #[must_use]
    pub fn new(interval: u64) -> Self {
        Self {
            checkpoints: BTreeMap::new(),
            interval,
            dir: None,
            last_persist_error: None,
        }
    }

    /// Create a checkpoint store that persists to a directory.
    #[must_use]
    pub fn with_dir(interval: u64, dir: PathBuf) -> Self {
        Self {
            checkpoints: BTreeMap::new(),
            interval,
            dir: Some(dir),
            last_persist_error: None,
        }
    }

    /// Record a checkpoint if `tick` hits the interval.
    pub fn maybe_checkpoint(&mut self, tick: u64, machine: &ProtocolMachine) {
        if self.interval == 0 || tick % self.interval != 0 {
            return;
        }
        self.last_persist_error = None;
        let data = match serde_json::to_vec(machine) {
            Ok(data) => data,
            Err(err) => {
                self.last_persist_error =
                    Some(format!("failed to serialize checkpoint {tick}: {err}"));
                return;
            }
        };

        self.checkpoints.insert(tick, data);
        if let Some(dir) = &self.dir {
            if let Err(err) = std::fs::create_dir_all(dir) {
                self.last_persist_error = Some(format!(
                    "failed to create checkpoint directory {dir:?}: {err}"
                ));
                return;
            }
            let path = dir.join(format!("checkpoint_{tick}.json"));
            if let Some(bytes) = self.checkpoints.get(&tick) {
                if let Err(err) = std::fs::write(&path, bytes) {
                    self.last_persist_error =
                        Some(format!("failed to persist checkpoint {path:?}: {err}"));
                }
            }
        }
    }

    /// Restore the ProtocolMachine state at a specific tick, if available.
    #[must_use]
    pub fn restore(&self, tick: u64) -> Option<ProtocolMachine> {
        self.checkpoints
            .get(&tick)
            .and_then(|data| serde_json::from_slice(data).ok())
    }

    /// Find the nearest checkpoint at or before the given tick.
    #[must_use]
    pub fn nearest_before(&self, tick: u64) -> Option<(u64, &SerializedState)> {
        self.checkpoints
            .range(..=tick)
            .next_back()
            .map(|(k, v)| (*k, v))
    }

    /// Last non-fatal persistence/serialization error observed by `maybe_checkpoint`.
    #[must_use]
    pub fn last_persist_error(&self) -> Option<&str> {
        self.last_persist_error.as_deref()
    }
}
