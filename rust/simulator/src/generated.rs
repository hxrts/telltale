use serde::{Deserialize, Serialize};
use serde_json::Value;
use telltale_protocol_machine::{ProtocolMachineSemanticObjects, SemanticAuditRecord};

/// Canonical simulator outcome classification for one generated effect step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ScenarioEffectDisposition {
    /// Return a successful payload.
    Return,
    /// Produce a timeout outcome.
    Timeout,
    /// Produce a cancellation outcome.
    Cancelled,
    /// Emit a stale late result that should fail closed.
    StaleLateResult,
    /// Report the effect as blocked.
    Blocked,
    /// Report degraded execution with additional detail.
    Degraded,
}

/// One scripted generated-effect step in a scenario.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ScenarioEffectStep {
    /// Declared effect interface name.
    pub interface_name: String,
    /// Declared effect operation name.
    pub operation_name: String,
    /// Requested simulator disposition.
    pub disposition: ScenarioEffectDisposition,
    /// Optional JSON payload for success or typed error shapes.
    #[serde(default)]
    pub payload: Option<Value>,
    /// Optional logical delay in milliseconds before the outcome resolves.
    #[serde(default)]
    pub delay_ms: Option<u64>,
    /// Optional degradation detail or diagnostic text.
    #[serde(default)]
    pub detail: Option<String>,
}

/// Scripted scenario for generated effect-family simulation.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct GeneratedEffectScenario {
    /// Ordered effect steps to drive through the simulator.
    pub steps: Vec<ScenarioEffectStep>,
}

impl GeneratedEffectScenario {
    /// Start building a scripted generated-effect scenario.
    #[must_use]
    pub fn builder() -> GeneratedEffectScenarioBuilder {
        GeneratedEffectScenarioBuilder::default()
    }
}

/// Builder for generated effect scenarios.
#[derive(Debug, Clone, Default)]
pub struct GeneratedEffectScenarioBuilder {
    steps: Vec<ScenarioEffectStep>,
}

impl GeneratedEffectScenarioBuilder {
    /// Record a successful effect result with a JSON payload.
    #[must_use]
    pub fn record_return(
        mut self,
        interface_name: impl Into<String>,
        operation_name: impl Into<String>,
        payload: Value,
    ) -> Self {
        self.steps.push(ScenarioEffectStep {
            interface_name: interface_name.into(),
            operation_name: operation_name.into(),
            disposition: ScenarioEffectDisposition::Return,
            payload: Some(payload),
            delay_ms: None,
            detail: None,
        });
        self
    }

    /// Record a timeout outcome.
    #[must_use]
    pub fn record_timeout(
        mut self,
        interface_name: impl Into<String>,
        operation_name: impl Into<String>,
    ) -> Self {
        self.steps.push(base_step(
            interface_name,
            operation_name,
            ScenarioEffectDisposition::Timeout,
        ));
        self
    }

    /// Record a cancellation outcome.
    #[must_use]
    pub fn record_cancelled(
        mut self,
        interface_name: impl Into<String>,
        operation_name: impl Into<String>,
    ) -> Self {
        self.steps.push(base_step(
            interface_name,
            operation_name,
            ScenarioEffectDisposition::Cancelled,
        ));
        self
    }

    /// Record a stale late result that should be rejected by the runtime.
    #[must_use]
    pub fn record_stale_late_result(
        mut self,
        interface_name: impl Into<String>,
        operation_name: impl Into<String>,
    ) -> Self {
        self.steps.push(base_step(
            interface_name,
            operation_name,
            ScenarioEffectDisposition::StaleLateResult,
        ));
        self
    }

    /// Record a blocked effect outcome.
    #[must_use]
    pub fn record_blocked(
        mut self,
        interface_name: impl Into<String>,
        operation_name: impl Into<String>,
    ) -> Self {
        self.steps.push(base_step(
            interface_name,
            operation_name,
            ScenarioEffectDisposition::Blocked,
        ));
        self
    }

    /// Record a degraded outcome with detail.
    #[must_use]
    pub fn record_degraded(
        mut self,
        interface_name: impl Into<String>,
        operation_name: impl Into<String>,
        detail: impl Into<String>,
    ) -> Self {
        let mut step = base_step(
            interface_name,
            operation_name,
            ScenarioEffectDisposition::Degraded,
        );
        step.detail = Some(detail.into());
        self.steps.push(step);
        self
    }

    /// Apply a delay to the most recently recorded step.
    #[must_use]
    pub fn with_delay_ms(mut self, delay_ms: u64) -> Self {
        if let Some(last) = self.steps.last_mut() {
            last.delay_ms = Some(delay_ms);
        }
        self
    }

    /// Finalize the scenario.
    #[must_use]
    pub fn build(self) -> GeneratedEffectScenario {
        GeneratedEffectScenario { steps: self.steps }
    }
}

/// Typed simulator helper result for one generated effect operation.
#[derive(Debug, Clone, PartialEq)]
pub enum ScenarioEffectResult<T> {
    /// Return a successful value, optionally delayed.
    Return {
        /// Returned value for the effect operation.
        value: T,
        /// Optional logical delay before the result resolves.
        delay_ms: Option<u64>,
    },
    /// Report a timeout, optionally delayed.
    Timeout {
        /// Optional logical delay before the timeout is observed.
        delay_ms: Option<u64>,
    },
    /// Report cancellation, optionally delayed.
    Cancelled {
        /// Optional logical delay before cancellation is observed.
        delay_ms: Option<u64>,
    },
    /// Report a stale late result, optionally delayed.
    StaleLateResult {
        /// Optional logical delay before the stale late result appears.
        delay_ms: Option<u64>,
    },
    /// Report a blocked effect, optionally delayed.
    Blocked {
        /// Optional logical delay before blocked status is observed.
        delay_ms: Option<u64>,
    },
    /// Report degradation with detail, optionally delayed.
    Degraded {
        /// Degradation detail attached to the effect outcome.
        detail: String,
        /// Optional logical delay before degradation is observed.
        delay_ms: Option<u64>,
    },
}

impl<T> ScenarioEffectResult<T> {
    /// Construct a successful result.
    #[must_use]
    pub fn success(value: T) -> Self {
        Self::Return {
            value,
            delay_ms: None,
        }
    }

    /// Construct a timeout result.
    #[must_use]
    pub fn timeout() -> Self {
        Self::Timeout { delay_ms: None }
    }

    /// Construct a cancellation result.
    #[must_use]
    pub fn cancelled() -> Self {
        Self::Cancelled { delay_ms: None }
    }

    /// Construct a stale late result.
    #[must_use]
    pub fn stale_late_result() -> Self {
        Self::StaleLateResult { delay_ms: None }
    }

    /// Construct a blocked result.
    #[must_use]
    pub fn blocked() -> Self {
        Self::Blocked { delay_ms: None }
    }

    /// Construct a degraded result.
    #[must_use]
    pub fn degraded(detail: impl Into<String>) -> Self {
        Self::Degraded {
            detail: detail.into(),
            delay_ms: None,
        }
    }

    /// Attach a delay to the result.
    #[must_use]
    pub fn with_delay_ms(self, delay_ms: u64) -> Self {
        match self {
            Self::Return { value, .. } => Self::Return {
                value,
                delay_ms: Some(delay_ms),
            },
            Self::Timeout { .. } => Self::Timeout {
                delay_ms: Some(delay_ms),
            },
            Self::Cancelled { .. } => Self::Cancelled {
                delay_ms: Some(delay_ms),
            },
            Self::StaleLateResult { .. } => Self::StaleLateResult {
                delay_ms: Some(delay_ms),
            },
            Self::Blocked { .. } => Self::Blocked {
                delay_ms: Some(delay_ms),
            },
            Self::Degraded { detail, .. } => Self::Degraded {
                detail,
                delay_ms: Some(delay_ms),
            },
        }
    }
}

/// Report tying a scripted generated-effect scenario to semantic runtime output.
#[derive(Debug, Clone, Default)]
pub struct GeneratedEffectSimulationReport {
    /// The scripted scenario that was executed.
    pub scenario: GeneratedEffectScenario,
    /// Canonical semantic objects emitted by the guest runtime.
    pub semantic_objects: ProtocolMachineSemanticObjects,
    /// Semantic audit records emitted while running the scenario.
    pub semantic_audit_log: Vec<SemanticAuditRecord>,
}

fn base_step(
    interface_name: impl Into<String>,
    operation_name: impl Into<String>,
    disposition: ScenarioEffectDisposition,
) -> ScenarioEffectStep {
    ScenarioEffectStep {
        interface_name: interface_name.into(),
        operation_name: operation_name.into(),
        disposition,
        payload: None,
        delay_ms: None,
        detail: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder_covers_failure_modes() {
        let scenario = GeneratedEffectScenario::builder()
            .record_return("Runtime", "acceptInvite", Value::String("ok".to_string()))
            .with_delay_ms(25)
            .record_timeout("Runtime", "acceptInvite")
            .record_cancelled("Runtime", "acceptInvite")
            .record_stale_late_result("Runtime", "acceptInvite")
            .record_blocked("Runtime", "acceptInvite")
            .record_degraded("Runtime", "acceptInvite", "owner_lag")
            .build();

        assert_eq!(scenario.steps.len(), 6);
        assert_eq!(scenario.steps[0].delay_ms, Some(25));
        assert_eq!(
            scenario.steps[5].disposition,
            ScenarioEffectDisposition::Degraded
        );
    }
}
