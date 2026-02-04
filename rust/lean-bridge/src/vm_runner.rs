//! Lean VM runner wrapper.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use thiserror::Error;

use crate::runner::ChoreographyJson;

/// Errors from Lean VM runner operations.
#[derive(Debug, Error)]
pub enum VmRunnerError {
    /// The VM runner binary was not found at the expected path.
    #[error("VM runner binary not found at {0}")]
    BinaryNotFound(PathBuf),
    /// Failed to create a temporary file for JSON exchange.
    #[error("Failed to create temp file: {0}")]
    TempFileError(#[from] std::io::Error),
    /// The Lean process exited with a non-zero status.
    #[error("VM runner failed with exit code {code}: {stderr}")]
    ProcessFailed {
        /// Exit code from the process.
        code: i32,
        /// Standard error output.
        stderr: String,
    },
    /// Failed to parse Lean output or JSON.
    #[error("Failed to parse VM runner output: {0}")]
    ParseError(String),
}

/// Input JSON for the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmRunInput {
    /// Choreographies to load.
    pub choreographies: Vec<ChoreographyJson>,
    /// Concurrency level.
    pub concurrency: usize,
    /// Maximum scheduler rounds.
    pub max_steps: usize,
}

/// One session status entry from the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmSessionStatus {
    /// Session id.
    pub sid: usize,
    /// Terminal flag.
    pub terminal: bool,
}

/// One trace event from the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmTraceEvent {
    pub kind: String,
    pub tick: u64,
    #[serde(default)]
    pub session: Option<usize>,
    #[serde(default)]
    pub sender: Option<String>,
    #[serde(default)]
    pub receiver: Option<String>,
    #[serde(default)]
    pub label: Option<String>,
    #[serde(default)]
    pub role: Option<String>,
    #[serde(default)]
    pub target: Option<String>,
    #[serde(default)]
    pub permitted: Option<bool>,
    #[serde(default)]
    pub epoch: Option<u64>,
    #[serde(default)]
    pub ghost: Option<usize>,
    #[serde(default)]
    pub from: Option<usize>,
    #[serde(default)]
    pub to: Option<usize>,
}

/// Output from the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmRunOutput {
    /// Observable trace.
    pub trace: Vec<VmTraceEvent>,
    /// Session statuses.
    pub sessions: Vec<VmSessionStatus>,
    /// Steps executed.
    pub steps_executed: u64,
    /// Concurrency level.
    pub concurrency: u64,
    /// Status string.
    pub status: String,
}

/// Runner for invoking the Lean VM runner binary.
pub struct VmRunner {
    binary_path: PathBuf,
}

impl VmRunner {
    /// Default path to the VM runner binary (relative to workspace root).
    pub const DEFAULT_BINARY_PATH: &'static str = "lean/.lake/build/bin/vm_runner";

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
            .filter(|p| p.exists())
    }

    /// Create a new VM runner with the default binary path.
    ///
    /// # Errors
    ///
    /// Returns [`VmRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn new() -> Result<Self, VmRunnerError> {
        match Self::get_binary_path() {
            Some(path) => Ok(Self { binary_path: path }),
            None => Err(VmRunnerError::BinaryNotFound(PathBuf::from(
                Self::DEFAULT_BINARY_PATH,
            ))),
        }
    }

    /// Create a VM runner with a custom binary path.
    ///
    /// # Errors
    ///
    /// Returns [`VmRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn with_binary_path(path: impl AsRef<Path>) -> Result<Self, VmRunnerError> {
        let binary_path = PathBuf::from(path.as_ref());
        if !binary_path.exists() {
            return Err(VmRunnerError::BinaryNotFound(binary_path));
        }
        Ok(Self { binary_path })
    }

    /// Try to create a runner, returning None if the binary is unavailable.
    #[must_use]
    pub fn try_new() -> Option<Self> {
        Self::new().ok()
    }

    /// Run the VM runner and return the parsed output.
    ///
    /// # Errors
    ///
    /// Returns a [`VmRunnerError`] if the process fails or output is invalid.
    pub fn run(&self, input: &VmRunInput) -> Result<VmRunOutput, VmRunnerError> {
        let payload = serde_json::to_vec(input).map_err(|e| VmRunnerError::ParseError(e.to_string()))?;

        let mut cmd = Command::new(&self.binary_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(VmRunnerError::TempFileError)?;

        if let Some(stdin) = cmd.stdin.as_mut() {
            stdin.write_all(&payload)?;
        }

        let output = cmd
            .wait_with_output()
            .map_err(VmRunnerError::TempFileError)?;

        if !output.status.success() {
            return Err(VmRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }

        let out: VmRunOutput = serde_json::from_slice(&output.stdout)
            .map_err(|e| VmRunnerError::ParseError(e.to_string()))?;
        Ok(out)
    }
}

/// Helper to build a VM runner input from JSON values.
#[must_use]
pub fn vm_input_from_values(
    choreographies: Vec<Value>,
    concurrency: usize,
    max_steps: usize,
) -> Result<VmRunInput, VmRunnerError> {
    let mut choreos = Vec::new();
    for value in choreographies {
        let choreo: ChoreographyJson = serde_json::from_value(value)
            .map_err(|e| VmRunnerError::ParseError(e.to_string()))?;
        choreos.push(choreo);
    }
    Ok(VmRunInput {
        choreographies: choreos,
        concurrency,
        max_steps,
    })
}

/// Serialize a VM runner output to JSON for debugging.
#[must_use]
pub fn output_to_json(output: &VmRunOutput) -> Value {
    serde_json::to_value(output).unwrap_or(Value::Null)
}
