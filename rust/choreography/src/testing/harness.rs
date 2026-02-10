//! Protocol Test Harness Implementation
//!
//! This module provides the core test harness functionality for
//! orchestrating multi-role protocol tests.

use crate::effects::ChoreographyError;
use crate::runtime::ChoreographicAdapter;
use crate::testing::RecordingObserver;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// Configuration for protocol tests.
#[derive(Debug, Clone)]
pub struct TestConfig {
    /// Timeout for the entire test.
    pub timeout: Duration,
    /// Whether to collect message trace.
    pub trace_messages: bool,
    /// Whether to collect phase events.
    pub trace_phases: bool,
    /// Maximum number of messages before aborting.
    pub max_messages: usize,
    /// Whether to fail fast on first error.
    pub fail_fast: bool,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            trace_messages: true,
            trace_phases: true,
            max_messages: 10000,
            fail_fast: false,
        }
    }
}

impl TestConfig {
    /// Create a new test config with default settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the timeout.
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Enable message tracing.
    pub fn with_message_tracing(mut self) -> Self {
        self.trace_messages = true;
        self
    }

    /// Disable message tracing.
    pub fn without_message_tracing(mut self) -> Self {
        self.trace_messages = false;
        self
    }

    /// Enable phase tracing.
    pub fn with_phase_tracing(mut self) -> Self {
        self.trace_phases = true;
        self
    }

    /// Disable phase tracing.
    pub fn without_phase_tracing(mut self) -> Self {
        self.trace_phases = false;
        self
    }

    /// Set maximum messages before aborting.
    pub fn max_messages(mut self, max: usize) -> Self {
        self.max_messages = max;
        self
    }

    /// Enable fail-fast mode (stop on first error).
    pub fn with_fail_fast(mut self) -> Self {
        self.fail_fast = true;
        self
    }

    /// Disable fail-fast mode (continue after errors).
    pub fn without_fail_fast(mut self) -> Self {
        self.fail_fast = false;
        self
    }
}

/// Binding of a role to an adapter for testing.
#[derive(Debug, Clone)]
pub struct RoleBinding {
    /// The role name.
    pub role_name: String,
    /// Optional role index for parameterized roles.
    pub index: Option<u32>,
}

impl RoleBinding {
    /// Create a new static role binding.
    pub fn new(role: impl Into<String>) -> Self {
        Self {
            role_name: role.into(),
            index: None,
        }
    }

    /// Create a new indexed role binding.
    pub fn indexed(role: impl Into<String>, index: u32) -> Self {
        Self {
            role_name: role.into(),
            index: Some(index),
        }
    }

    /// Get the display name (e.g., `Witness[2]` for indexed roles).
    #[must_use]
    pub fn display_name(&self) -> String {
        match self.index {
            Some(i) => format!("{}[{}]", self.role_name, i),
            None => self.role_name.clone(),
        }
    }
}

/// Result of running a protocol test.
#[derive(Debug)]
pub struct TestResult {
    /// Whether the test completed successfully.
    pub success: bool,
    /// Errors encountered during the test.
    pub errors: Vec<ChoreographyError>,
    /// Role-specific outputs (as serialized bytes).
    pub outputs: HashMap<String, Vec<u8>>,
    /// Message trace (if enabled).
    pub messages: Vec<MessageRecord>,
    /// Phase events (if enabled).
    pub phases: Vec<PhaseRecord>,
    /// Total execution time.
    pub duration: Duration,
}

impl TestResult {
    /// Create a new successful result.
    pub fn success() -> Self {
        Self {
            success: true,
            errors: Vec::new(),
            outputs: HashMap::new(),
            messages: Vec::new(),
            phases: Vec::new(),
            duration: Duration::ZERO,
        }
    }

    /// Create a new failed result.
    pub fn failure(errors: Vec<ChoreographyError>) -> Self {
        Self {
            success: false,
            errors,
            outputs: HashMap::new(),
            messages: Vec::new(),
            phases: Vec::new(),
            duration: Duration::ZERO,
        }
    }

    /// Check if the test completed successfully.
    #[must_use]
    pub fn completed_successfully(&self) -> bool {
        self.success && self.errors.is_empty()
    }

    /// Get the number of phases completed.
    #[must_use]
    pub fn phase_count(&self) -> usize {
        self.phases.iter().filter(|p| p.completed).count()
    }

    /// Get the number of messages exchanged.
    #[must_use]
    pub fn message_count(&self) -> usize {
        self.messages.len()
    }

    /// Get raw output bytes for a specific role.
    #[must_use]
    pub fn role_output(&self, role: &str) -> Option<&[u8]> {
        self.outputs.get(role).map(|v| v.as_slice())
    }

    /// Deserialize output for a specific role.
    pub fn deserialize_output<T: serde::de::DeserializeOwned>(
        &self,
        role: &str,
    ) -> Option<Result<T, bincode::Error>> {
        self.outputs
            .get(role)
            .map(|bytes| bincode::deserialize(bytes))
    }

    /// Get all message traces.
    #[must_use]
    pub fn message_trace(&self) -> &[MessageRecord] {
        &self.messages
    }

    /// Get all phase records.
    #[must_use]
    pub fn phase_trace(&self) -> &[PhaseRecord] {
        &self.phases
    }

    /// Get messages between specific roles.
    pub fn messages_between(&self, from: &str, to: &str) -> Vec<&MessageRecord> {
        self.messages
            .iter()
            .filter(|m| m.from == from && m.to == to)
            .collect()
    }

    /// Get the first error, if any.
    #[must_use]
    pub fn first_error(&self) -> Option<&ChoreographyError> {
        self.errors.first()
    }
}

/// Record of a message exchanged during the test.
#[derive(Debug, Clone)]
pub struct MessageRecord {
    /// Sender role.
    pub from: String,
    /// Receiver role.
    pub to: String,
    /// Message type name.
    pub message_type: String,
    /// Message size in bytes.
    pub size: usize,
    /// Timestamp when sent.
    pub timestamp: std::time::Instant,
}

/// Record of a phase execution.
#[derive(Debug, Clone)]
pub struct PhaseRecord {
    /// Protocol name.
    pub protocol: String,
    /// Role name.
    pub role: String,
    /// Phase name.
    pub phase: String,
    /// Whether the phase completed.
    pub completed: bool,
    /// Phase duration.
    pub duration: Duration,
}

/// Builder for protocol tests.
#[derive(Debug)]
pub struct ProtocolTestBuilder {
    /// Protocol name.
    protocol_name: String,
    /// Role bindings (role name -> list of bindings for indexed roles).
    role_bindings: HashMap<String, Vec<RoleBinding>>,
    /// Expected phases to complete.
    expected_phases: Vec<String>,
    /// Test configuration.
    config: TestConfig,
    /// Parameters for the test (serialized as bytes).
    params: Option<Vec<u8>>,
}

impl ProtocolTestBuilder {
    /// Create a new test builder for the given protocol.
    pub fn new(protocol_name: impl Into<String>) -> Self {
        Self {
            protocol_name: protocol_name.into(),
            role_bindings: HashMap::new(),
            expected_phases: Vec::new(),
            config: TestConfig::default(),
            params: None,
        }
    }

    /// Bind a static role.
    pub fn bind_role(mut self, role: impl Into<String>) -> Self {
        let role_name = role.into();
        self.role_bindings
            .entry(role_name.clone())
            .or_default()
            .push(RoleBinding::new(role_name));
        self
    }

    /// Bind multiple instances of an indexed role.
    pub fn bind_roles(mut self, role: impl Into<String>, count: usize) -> Self {
        let role_name = role.into();
        let bindings: Vec<_> = (0..count)
            .map(|i| RoleBinding::indexed(role_name.clone(), i as u32))
            .collect();
        self.role_bindings
            .entry(role_name)
            .or_default()
            .extend(bindings);
        self
    }

    /// Set test parameters (serialized).
    pub fn with_params_bytes(mut self, params: Vec<u8>) -> Self {
        self.params = Some(params);
        self
    }

    /// Set test parameters from a serializable value.
    pub fn with_params<T: serde::Serialize>(mut self, params: &T) -> Result<Self, bincode::Error> {
        self.params = Some(bincode::serialize(params)?);
        Ok(self)
    }

    /// Set expected phases.
    pub fn expect_phases(mut self, phases: &[&str]) -> Self {
        self.expected_phases = phases.iter().map(|s| (*s).to_string()).collect();
        self
    }

    /// Set test configuration.
    pub fn with_config(mut self, config: TestConfig) -> Self {
        self.config = config;
        self
    }

    /// Set timeout.
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    /// Build the test.
    pub fn build(self) -> ProtocolTest {
        ProtocolTest {
            protocol_name: self.protocol_name,
            role_bindings: self.role_bindings,
            expected_phases: self.expected_phases,
            config: self.config,
            params: self.params,
            observer: Arc::new(Mutex::new(RecordingObserver::new())),
        }
    }
}

/// Protocol test runner.
#[derive(Debug)]
pub struct ProtocolTest {
    /// Protocol name.
    protocol_name: String,
    /// Role bindings.
    role_bindings: HashMap<String, Vec<RoleBinding>>,
    /// Expected phases.
    expected_phases: Vec<String>,
    /// Configuration.
    config: TestConfig,
    /// Parameters (serialized bytes).
    params: Option<Vec<u8>>,
    /// Observer for recording events.
    observer: Arc<Mutex<RecordingObserver>>,
}

impl ProtocolTest {
    /// Create a new test builder.
    pub fn builder(protocol_name: impl Into<String>) -> ProtocolTestBuilder {
        ProtocolTestBuilder::new(protocol_name)
    }

    /// Get the protocol name.
    #[must_use]
    pub fn protocol_name(&self) -> &str {
        &self.protocol_name
    }

    /// Get the role bindings.
    #[must_use]
    pub fn role_bindings(&self) -> &HashMap<String, Vec<RoleBinding>> {
        &self.role_bindings
    }

    /// Get the expected phases.
    #[must_use]
    pub fn expected_phases(&self) -> &[String] {
        &self.expected_phases
    }

    /// Get the configuration.
    #[must_use]
    pub fn config(&self) -> &TestConfig {
        &self.config
    }

    /// Get the raw test parameters bytes.
    #[must_use]
    pub fn params_bytes(&self) -> Option<&[u8]> {
        self.params.as_deref()
    }

    /// Deserialize the test parameters.
    pub fn params<T: serde::de::DeserializeOwned>(&self) -> Option<Result<T, bincode::Error>> {
        self.params
            .as_ref()
            .map(|bytes| bincode::deserialize(bytes))
    }

    /// Run the test (placeholder - actual implementation depends on protocol).
    ///
    /// This is a framework method that sets up the test infrastructure.
    /// The actual execution logic is provided by generated protocol code.
    pub async fn run(self) -> Result<TestResult, ChoreographyError> {
        let start = std::time::Instant::now();

        // Validate bindings
        if self.role_bindings.is_empty() {
            return Err(ChoreographyError::ExecutionError(
                "No role bindings provided".to_string(),
            ));
        }

        // Create result
        let mut result = TestResult::success();
        result.duration = start.elapsed();

        // Collect observer events
        // Track phase start times for duration calculation
        let mut phase_start_times: HashMap<(String, String, String), std::time::Instant> =
            HashMap::new();

        let observer = self.observer.lock().unwrap();
        for event in observer.events() {
            match event {
                crate::testing::observer::ProtocolEvent::Send {
                    from,
                    to,
                    msg_type,
                    size,
                } => {
                    if self.config.trace_messages {
                        result.messages.push(MessageRecord {
                            from: from.clone(),
                            to: to.clone(),
                            message_type: msg_type.clone(),
                            size: *size,
                            timestamp: std::time::Instant::now(),
                        });
                    }
                }
                crate::testing::observer::ProtocolEvent::PhaseStart {
                    protocol,
                    role,
                    phase,
                } => {
                    // Record phase start time
                    let key = (protocol.clone(), role.clone(), phase.clone());
                    phase_start_times.insert(key, std::time::Instant::now());
                }
                crate::testing::observer::ProtocolEvent::PhaseEnd {
                    protocol,
                    role,
                    phase,
                } => {
                    if self.config.trace_phases {
                        // Calculate duration from phase start
                        let key = (protocol.clone(), role.clone(), phase.clone());
                        let duration = phase_start_times
                            .remove(&key)
                            .map(|start| start.elapsed())
                            .unwrap_or(Duration::ZERO);

                        result.phases.push(PhaseRecord {
                            protocol: protocol.clone(),
                            role: role.clone(),
                            phase: phase.clone(),
                            completed: true,
                            duration,
                        });
                    }
                }
                _ => {}
            }
        }

        // Verify expected phases
        if !self.expected_phases.is_empty() {
            let completed_phases: Vec<_> = result
                .phases
                .iter()
                .filter(|p| p.completed)
                .map(|p| p.phase.as_str())
                .collect();

            for expected in &self.expected_phases {
                if !completed_phases.contains(&expected.as_str()) {
                    result
                        .errors
                        .push(ChoreographyError::ExecutionError(format!(
                            "Expected phase '{}' was not completed",
                            expected
                        )));
                }
            }
        }

        result.success = result.errors.is_empty();
        Ok(result)
    }
}

/// Trait for adapters that can be used in protocol tests.
pub trait TestableAdapter: ChoreographicAdapter {
    /// Reset the adapter state for a new test.
    fn reset(&mut self);

    /// Get a name for this adapter instance.
    fn name(&self) -> &str;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_builder() {
        let config = TestConfig::new()
            .timeout(Duration::from_secs(60))
            .without_message_tracing()
            .max_messages(100)
            .with_fail_fast();

        assert_eq!(config.timeout, Duration::from_secs(60));
        assert!(!config.trace_messages);
        assert_eq!(config.max_messages, 100);
        assert!(config.fail_fast);
    }

    #[test]
    fn test_role_binding() {
        let static_binding = RoleBinding::new("Coordinator");
        assert!(static_binding.index.is_none());

        let indexed_binding = RoleBinding::indexed("Witness", 2);
        assert_eq!(indexed_binding.index, Some(2));
    }

    #[test]
    fn test_protocol_test_builder() {
        let test = ProtocolTest::builder("TestProtocol")
            .bind_role("Coordinator")
            .bind_roles("Witness", 3)
            .expect_phases(&["init", "commit"])
            .timeout(Duration::from_secs(10))
            .build();

        assert_eq!(test.protocol_name(), "TestProtocol");
        assert!(test.role_bindings().contains_key("Coordinator"));
        assert_eq!(test.role_bindings()["Witness"].len(), 3);
        assert_eq!(test.expected_phases().len(), 2);
    }

    #[test]
    fn test_result_accessors() {
        let mut result = TestResult::success();
        result.messages.push(MessageRecord {
            from: "A".to_string(),
            to: "B".to_string(),
            message_type: "Request".to_string(),
            size: 100,
            timestamp: std::time::Instant::now(),
        });
        result.phases.push(PhaseRecord {
            protocol: "Test".to_string(),
            role: "A".to_string(),
            phase: "init".to_string(),
            completed: true,
            duration: Duration::from_millis(50),
        });

        assert!(result.completed_successfully());
        assert_eq!(result.message_count(), 1);
        assert_eq!(result.phase_count(), 1);
        assert_eq!(result.messages_between("A", "B").len(), 1);
    }
}
