//! Lean heap parity runner wrapper.

use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::thread;
use std::time::{Duration, Instant};
use thiserror::Error;

/// Errors from Lean heap parity runner operations.
#[derive(Debug, Error)]
pub enum HeapParityRunnerError {
    /// The Lean heap parity runner binary was not found.
    #[error("Lean heap parity runner binary not found at {0}")]
    BinaryNotFound(PathBuf),
    /// The Lean process exited with a non-zero status.
    #[error("Lean heap parity runner failed with exit code {code}: {stderr}")]
    ProcessFailed { code: i32, stderr: String },
    /// Failed to parse Lean output.
    #[error("Failed to parse Lean heap parity output: {0}")]
    ParseError(String),
    /// The Lean process timed out.
    #[error("Lean heap parity runner '{operation}' timed out after {timeout_ms}ms")]
    TimedOut {
        operation: String,
        timeout_ms: u64,
    },
    /// IO error while invoking the process.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityResourceFixtureOutput {
    pub canonical_bytes_hex: String,
    pub resource_id_preimage_hex: String,
    pub resource_leaf_preimage_hex: String,
    pub nullifier_leaf_preimage_hex: String,
    pub resource_id_digest_hex: String,
    pub nullifier_leaf_hex: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityProofStep {
    pub direction: String,
    pub sibling_hash_hex: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityProof {
    pub leaf_hash_hex: String,
    pub path: Vec<HeapParityProofStep>,
    pub root_hex: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityResourceId {
    pub digest_hex: String,
    pub counter: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityStateSummary {
    pub active_resource_ids: Vec<HeapParityResourceId>,
    pub consumed_resource_ids: Vec<HeapParityResourceId>,
    pub counter: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityCommitment {
    pub resource_root_hex: String,
    pub nullifier_root_hex: String,
    pub counter: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityHeapFixtureOutput {
    pub active_resource_ids_hex: Vec<String>,
    pub consumed_resource_ids_hex: Vec<String>,
    pub proof_index: u64,
    pub resource_proof: Option<HeapParityProof>,
    pub nullifier_proof: Option<HeapParityProof>,
    pub merkle_node_preimage_hex: String,
    pub heap_commitment: HeapParityCommitment,
    pub heap_commitment_preimage_hex: String,
    pub commitment_hash_hex: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityReplayOutput {
    pub first_run: HeapParityStateSummary,
    pub second_run: HeapParityStateSummary,
    pub stable: bool,
    pub active_ids_match_fixture: bool,
    pub consumed_ids_match_fixture: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HeapParityOutput {
    pub schema_version: String,
    pub heap_encoding_version: u16,
    pub hasher: String,
    pub resource_fixture: HeapParityResourceFixtureOutput,
    pub heap_fixture: HeapParityHeapFixtureOutput,
    pub replay: HeapParityReplayOutput,
}

/// Runner for invoking the Lean heap parity executable.
pub struct HeapParityRunner {
    binary_path: PathBuf,
}

impl HeapParityRunner {
    /// Default path to the Lean binary.
    pub const DEFAULT_BINARY_PATH: &'static str = "lean/.lake/build/bin/heap_parity_runner";
    /// Default timeout for heap parity invocations.
    pub const DEFAULT_TIMEOUT_MS: u64 = 120_000;

    fn process_timeout() -> Duration {
        let ms = std::env::var("TELLTALE_LEAN_TIMEOUT_MS")
            .ok()
            .and_then(|raw| raw.parse::<u64>().ok())
            .unwrap_or(Self::DEFAULT_TIMEOUT_MS);
        Duration::from_millis(ms.max(1))
    }

    fn wait_with_timeout(
        mut child: Child,
        timeout: Duration,
        operation: &str,
    ) -> Result<Output, HeapParityRunnerError> {
        let start = Instant::now();
        loop {
            match child.try_wait()? {
                Some(_) => return child.wait_with_output().map_err(HeapParityRunnerError::from),
                None => {
                    if start.elapsed() >= timeout {
                        if let Err(err) = child.kill() {
                            eprintln!(
                                "best-effort child.kill failed during timeout handling: {err}"
                            );
                        }
                        if let Err(err) = child.wait() {
                            eprintln!(
                                "best-effort child.wait failed during timeout handling: {err}"
                            );
                        }
                        return Err(HeapParityRunnerError::TimedOut {
                            operation: operation.to_string(),
                            timeout_ms: u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX),
                        });
                    }
                    thread::sleep(Duration::from_millis(10));
                }
            }
        }
    }

    fn run_command_with_timeout(
        &self,
        mut command: Command,
        operation: &str,
    ) -> Result<Output, HeapParityRunnerError> {
        command.stdout(Stdio::piped());
        command.stderr(Stdio::piped());
        let child = command.spawn()?;
        Self::wait_with_timeout(child, Self::process_timeout(), operation)
    }

    fn find_workspace_root() -> Option<PathBuf> {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let mut path = PathBuf::from(manifest_dir);
        for _ in 0..5 {
            if path.join("lean/.lake").is_dir() {
                return Some(path);
            }
            if !path.pop() {
                break;
            }
        }
        None
    }

    fn get_binary_path() -> Option<PathBuf> {
        Self::find_workspace_root()
            .map(|root| root.join(Self::DEFAULT_BINARY_PATH))
            .filter(|path| path.exists())
    }

    /// Create a new runner using the default binary path.
    pub fn new() -> Result<Self, HeapParityRunnerError> {
        match Self::get_binary_path() {
            Some(path) => Ok(Self { binary_path: path }),
            None => Err(HeapParityRunnerError::BinaryNotFound(PathBuf::from(
                Self::DEFAULT_BINARY_PATH,
            ))),
        }
    }

    /// Create a runner with a custom binary path.
    pub fn with_binary_path(path: impl AsRef<Path>) -> Result<Self, HeapParityRunnerError> {
        let binary_path = PathBuf::from(path.as_ref());
        if !binary_path.exists() || !binary_path.is_file() {
            return Err(HeapParityRunnerError::BinaryNotFound(binary_path));
        }
        Ok(Self { binary_path })
    }

    /// Try to create a runner, returning `None` when the binary is unavailable.
    #[must_use]
    pub fn try_new() -> Option<Self> {
        Self::new().ok()
    }

    /// Check whether the heap parity runner binary is available.
    #[must_use]
    pub fn is_available() -> bool {
        Self::get_binary_path().is_some()
    }

    /// Require that the heap parity runner is available.
    pub fn require_available() {
        if !Self::is_available() {
            panic!(
                "Lean heap parity runner required but unavailable. Run `cd lean && lake build heap_parity_runner`."
            );
        }
    }

    /// Run the heap parity fixture through the Lean executable.
    pub fn run_fixture(
        &self,
        fixture_path: impl AsRef<Path>,
    ) -> Result<HeapParityOutput, HeapParityRunnerError> {
        let mut command = Command::new(&self.binary_path);
        command.arg(fixture_path.as_ref());
        let output = self.run_command_with_timeout(command, "run_fixture")?;
        if !output.status.success() {
            return Err(HeapParityRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            });
        }
        serde_json::from_slice(&output.stdout)
            .map_err(|err| HeapParityRunnerError::ParseError(err.to_string()))
    }
}
