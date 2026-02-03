//! VM state checkpoints for replay and debugging.

use std::collections::BTreeMap;
use std::path::PathBuf;

use telltale_vm::vm::VM;

/// Serialized VM state blob.
pub type SerializedState = Vec<u8>;

/// Periodic VM state snapshots for replay and debugging.
pub struct CheckpointStore {
    checkpoints: BTreeMap<u64, SerializedState>,
    interval: u64,
    dir: Option<PathBuf>,
}

impl CheckpointStore {
    /// Create a new checkpoint store.
    #[must_use]
    pub fn new(interval: u64) -> Self {
        Self {
            checkpoints: BTreeMap::new(),
            interval,
            dir: None,
        }
    }

    /// Create a checkpoint store that persists to a directory.
    #[must_use]
    pub fn with_dir(interval: u64, dir: PathBuf) -> Self {
        Self {
            checkpoints: BTreeMap::new(),
            interval,
            dir: Some(dir),
        }
    }

    /// Record a checkpoint if `tick` hits the interval.
    pub fn maybe_checkpoint(&mut self, tick: u64, vm: &VM) {
        if self.interval == 0 || tick % self.interval != 0 {
            return;
        }
        if let Ok(data) = serde_json::to_vec(vm) {
            self.checkpoints.insert(tick, data);
            if let Some(dir) = &self.dir {
                if std::fs::create_dir_all(dir).is_ok() {
                    let path = dir.join(format!("checkpoint_{tick}.json"));
                    if let Err(_err) = std::fs::write(path, self.checkpoints.get(&tick).unwrap()) {
                        // Best-effort persistence only.
                    }
                }
            }
        }
    }

    /// Restore the VM state at a specific tick, if available.
    #[must_use]
    pub fn restore(&self, tick: u64) -> Option<VM> {
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
}
