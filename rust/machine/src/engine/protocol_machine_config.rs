/// Runtime host-contract assertion mode.
///
/// Production configurations should use [`HostContractMode::Enforced`]. The
/// relaxed mode exists for tests that intentionally violate handler identity,
/// topology ordering, or transfer-audit contracts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HostContractMode {
    /// Enforce host integration contracts at runtime.
    #[default]
    Enforced,
    /// Disable host integration assertions for targeted tests only.
    RelaxedTestOnly,
}

impl HostContractMode {
    /// Whether runtime host-contract assertions are enabled.
    #[must_use]
    pub const fn is_enforced(self) -> bool {
        matches!(self, Self::Enforced)
    }
}

fn deserialize_host_contract_mode<'de, D>(deserializer: D) -> Result<HostContractMode, D::Error>
where
    D: Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum Compat {
        Bool(bool),
        Mode(HostContractMode),
    }

    Ok(match Compat::deserialize(deserializer)? {
        Compat::Bool(true) => HostContractMode::Enforced,
        Compat::Bool(false) => HostContractMode::RelaxedTestOnly,
        Compat::Mode(mode) => mode,
    })
}

/// ProtocolMachine configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolMachineConfig {
    /// Migration-safe config schema version.
    #[serde(default = "default_config_schema_version")]
    pub config_schema_version: u32,
    /// Scheduling policy.
    pub sched_policy: SchedPolicy,
    /// Default buffer configuration for new sessions.
    pub buffer_config: BufferConfig,
    /// Maximum number of concurrent sessions.
    pub max_sessions: usize,
    /// Maximum number of concurrent coroutines.
    pub max_coroutines: usize,
    /// Number of registers per coroutine.
    pub num_registers: u16,
    /// Simulated time per scheduler round.
    pub tick_duration: Duration,
    /// Guard layers configured for the ProtocolMachine.
    pub guard_layers: Vec<GuardLayerConfig>,
    /// Whether speculative execution is enabled.
    pub speculation_enabled: bool,
    /// Determinism profile for replay/equivalence behavior.
    pub determinism_mode: DeterminismMode,
    /// Effect determinism tier used by admission and envelope artifacts.
    #[serde(default)]
    pub effect_determinism_tier: EffectDeterminismTier,
    /// Output-condition policy for commit eligibility of observable outputs.
    pub output_condition_policy: OutputConditionPolicy,
    /// Monitor mode for pre-dispatch type checks.
    #[serde(default)]
    pub monitor_mode: MonitorMode,
    /// Flow policy for epistemic knowledge checks.
    #[serde(default)]
    pub flow_policy: FlowPolicy,
    /// Deterministic cost charged for each instruction dispatch.
    #[serde(default = "default_instruction_cost")]
    pub instruction_cost: usize,
    /// Initial cost budget assigned to each coroutine.
    #[serde(default = "default_initial_cost_budget")]
    pub initial_cost_budget: usize,
    /// Whether threaded scheduler may admit same-session picks when footprint-disjoint.
    #[serde(default)]
    pub footprint_guided_wave_widening: bool,
    /// Runtime tuning profile used by instrumentation/benchmark harnesses.
    #[serde(default)]
    pub runtime_tuning_profile: RuntimeTuningProfile,
    /// Round semantics mode used by threaded scheduler.
    #[serde(default)]
    pub threaded_round_semantics: ThreadedRoundSemantics,
    /// Effect-trace capture mode for integration/perf tuning.
    #[serde(default)]
    pub effect_trace_capture_mode: EffectTraceCaptureMode,
    /// Retention policy for observable and diagnostic artifacts.
    #[serde(default)]
    pub observability_retention: ObservabilityRetentionConfig,
    /// Runtime payload hardening mode for inbound/outbound messages.
    #[serde(default)]
    pub payload_validation_mode: PayloadValidationMode,
    /// Communication replay-consumption mode.
    #[serde(default)]
    pub communication_replay_mode: CommunicationReplayMode,
    /// Upper bound for ProtocolMachine payload values in estimated wire bytes.
    #[serde(default = "default_max_payload_bytes")]
    pub max_payload_bytes: usize,
    /// Runtime host-contract assertion mode with deterministic diagnostics.
    #[serde(
        default = "default_host_contract_assertions",
        deserialize_with = "deserialize_host_contract_mode"
    )]
    pub host_contract_assertions: HostContractMode,
}

fn default_host_contract_assertions() -> HostContractMode {
    HostContractMode::Enforced
}

impl Default for ProtocolMachineConfig {
    fn default() -> Self {
        Self {
            config_schema_version: default_config_schema_version(),
            sched_policy: SchedPolicy::Cooperative,
            buffer_config: BufferConfig::default(),
            max_sessions: 256,
            max_coroutines: 1024,
            num_registers: 16,
            tick_duration: Duration::from_millis(1),
            guard_layers: Vec::new(),
            speculation_enabled: false,
            determinism_mode: DeterminismMode::Full,
            effect_determinism_tier: EffectDeterminismTier::StrictDeterministic,
            output_condition_policy: OutputConditionPolicy::AllowAll,
            monitor_mode: MonitorMode::SessionTypePrecheck,
            flow_policy: FlowPolicy::AllowAll,
            instruction_cost: 1,
            initial_cost_budget: usize::MAX,
            footprint_guided_wave_widening: false,
            runtime_tuning_profile: RuntimeTuningProfile::Standard,
            threaded_round_semantics: ThreadedRoundSemantics::CanonicalOneStep,
            effect_trace_capture_mode: EffectTraceCaptureMode::Full,
            observability_retention: ObservabilityRetentionConfig::default(),
            payload_validation_mode: PayloadValidationMode::Structural,
            communication_replay_mode: CommunicationReplayMode::Off,
            max_payload_bytes: default_max_payload_bytes(),
            host_contract_assertions: default_host_contract_assertions(),
        }
    }
}

impl ProtocolMachineConfig {
    /// Validate ProtocolMachine configuration invariants required for safe state initialization.
    ///
    /// # Errors
    ///
    /// Returns a reason string if a required invariant is violated.
    pub fn validate_invariants(&self) -> Result<(), String> {
        if self.config_schema_version < 1 {
            return Err("config_schema_version must be >= 1".to_string());
        }
        if self.max_sessions == 0 {
            return Err("max_sessions must be > 0".to_string());
        }
        if self.max_coroutines == 0 {
            return Err("max_coroutines must be > 0".to_string());
        }
        if self.num_registers == 0 {
            return Err("num_registers must be > 0".to_string());
        }
        if self.instruction_cost == 0 {
            return Err("instruction_cost must be > 0".to_string());
        }
        if self.max_payload_bytes == 0 {
            return Err("max_payload_bytes must be > 0".to_string());
        }
        if self.observability_retention.mode == ObservabilityRetentionMode::Capped
            && self.observability_retention.capacity == 0
        {
            return Err("observability_retention.capacity must be > 0 in capped mode".to_string());
        }
        if self.determinism_mode == DeterminismMode::Full
            && self.host_contract_assertions == HostContractMode::RelaxedTestOnly
        {
            return Err(
                "host_contract_assertions=relaxed_test_only is not valid with DeterminismMode::Full"
                    .to_string(),
            );
        }
        Ok(())
    }

    /// Assert ProtocolMachine configuration invariants required for safe state initialization.
    ///
    /// # Panics
    ///
    /// Panics when a required invariant is violated.
    pub fn assert_invariants(&self) {
        if let Err(reason) = self.validate_invariants() {
            panic!("{reason}");
        }
    }

    /// Deterministic baseline profile with minimal retained instrumentation.
    #[must_use]
    pub fn strict_minimal() -> Self {
        Self {
            determinism_mode: DeterminismMode::Full,
            threaded_round_semantics: ThreadedRoundSemantics::CanonicalOneStep,
            effect_trace_capture_mode: EffectTraceCaptureMode::Disabled,
            payload_validation_mode: PayloadValidationMode::Structural,
            communication_replay_mode: CommunicationReplayMode::Off,
            observability_retention: ObservabilityRetentionConfig {
                mode: ObservabilityRetentionMode::Capped,
                capacity: 1_024,
            },
            ..Self::default()
        }
    }

    /// Deterministic profile with full observable/effect tracing enabled.
    #[must_use]
    pub fn strict_observable() -> Self {
        Self {
            effect_trace_capture_mode: EffectTraceCaptureMode::Full,
            observability_retention: ObservabilityRetentionConfig::default(),
            ..Self::strict_minimal()
        }
    }

    /// Deterministic profile with strict validation and replay tracking enabled.
    #[must_use]
    pub fn strict_verified() -> Self {
        Self {
            effect_trace_capture_mode: EffectTraceCaptureMode::Full,
            payload_validation_mode: PayloadValidationMode::StrictSchema,
            communication_replay_mode: CommunicationReplayMode::Nullifier,
            observability_retention: ObservabilityRetentionConfig::default(),
            ..Self::strict_minimal()
        }
    }

    /// Deterministic churn profile for repeated short-lived sessions.
    #[must_use]
    pub fn strict_churn() -> Self {
        Self {
            observability_retention: ObservabilityRetentionConfig {
                mode: ObservabilityRetentionMode::Capped,
                capacity: 256,
            },
            ..Self::strict_minimal()
        }
    }

    /// Deterministic buffer-pressure profile for allocator and queue stress.
    #[must_use]
    pub fn strict_buffer_pressure() -> Self {
        Self {
            buffer_config: BufferConfig {
                mode: crate::buffer::BufferMode::Fifo,
                initial_capacity: 1,
                policy: crate::buffer::BackpressurePolicy::Resize { max_capacity: 8 },
            },
            ..Self::strict_minimal()
        }
    }

    /// Deterministic large-fanout profile for scheduler and metadata scaling tests.
    #[must_use]
    pub fn strict_large_fanout() -> Self {
        Self {
            observability_retention: ObservabilityRetentionConfig {
                mode: ObservabilityRetentionMode::Capped,
                capacity: 4_096,
            },
            ..Self::strict_minimal()
        }
    }
}

/// Observable event emitted by the ProtocolMachine.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TickedObsEvent {
    /// Scheduler tick when the wrapped event occurred.
    pub tick: u64,
    /// Underlying observable event payload.
    pub event: ObsEvent,
}

/// Observable event emitted by the ProtocolMachine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SessionTerminalReason {
    /// Session closed normally.
    Closed {
        /// Deterministic terminal explanation recorded in the trace.
        reason: String,
    },
    /// Session cancelled through an explicit cancellation path.
    Cancelled {
        /// Deterministic terminal explanation recorded in the trace.
        reason: String,
    },
    /// Session aborted through an explicit abort path.
    Aborted {
        /// Deterministic terminal explanation recorded in the trace.
        reason: String,
    },
    /// Session faulted with an explicit terminal reason.
    Faulted {
        /// Deterministic terminal explanation recorded in the trace.
        reason: String,
    },
}

/// Observable event emitted by the ProtocolMachine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObsEvent {
    /// Value sent on an edge.
    Sent {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this send.
        edge: Edge,
        /// Session ID.
        session: SessionId,
        /// Sender role.
        from: String,
        /// Receiver role.
        to: String,
        /// Message label.
        label: String,
    },
    /// Value received on an edge.
    Received {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this receive.
        edge: Edge,
        /// Session ID.
        session: SessionId,
        /// Sender role.
        from: String,
        /// Receiver role.
        to: String,
        /// Message label.
        label: String,
    },
    /// Label offered on an edge.
    Offered {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this offer.
        edge: Edge,
        /// Label offered.
        label: String,
    },
    /// Label chosen on an edge.
    Chose {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this choice.
        edge: Edge,
        /// Label chosen.
        label: String,
    },
    /// Session opened.
    Opened {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Participating roles.
        roles: Vec<String>,
    },
    /// Session closed.
    Closed {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
    },
    /// Explicit terminal transition for one session.
    SessionTerminal {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Explicit terminal reason.
        reason: SessionTerminalReason,
    },
    /// Session epoch advanced.
    EpochAdvanced {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        sid: SessionId,
        /// New epoch number.
        epoch: usize,
    },
    /// Coroutine halted.
    Halted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
    },
    /// Effect handler invoked.
    Invoked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
        /// Role name.
        role: String,
    },
    /// Guard layer acquired.
    Acquired {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Guard layer identifier.
        layer: String,
    },
    /// Guard layer released.
    Released {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Guard layer identifier.
        layer: String,
    },
    /// Endpoint transferred between coroutines.
    Transferred {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Source coroutine.
        from: usize,
        /// Target coroutine.
        to: usize,
    },
    /// Speculation forked for a ghost session.
    Forked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Ghost session id.
        ghost: usize,
    },
    /// Speculation joined.
    Joined {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
    },
    /// Speculation aborted.
    Aborted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
    },
    /// Knowledge fact tagged.
    Tagged {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Fact payload.
        fact: String,
    },
    /// Knowledge fact checked.
    Checked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Target role.
        target: String,
        /// Whether the flow policy permitted the fact.
        permitted: bool,
    },
    /// Coroutine faulted.
    Faulted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
        /// The fault.
        fault: Fault,
    },
    /// Typed failure branch entry became visible before terminal fault handling.
    FailureBranchEntered {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Coroutine ID.
        coro_id: usize,
        /// Failure that entered the branch.
        fault: Fault,
    },
    /// Explicit timeout occurrence became active for one site.
    TimeoutIssued {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Site that timed out.
        site: String,
        /// Tick until which the timeout remains active.
        until_tick: u64,
        /// Timeout witness issued for the occurrence.
        witness_id: AuthorityWitnessId,
    },
    /// Explicit cancellation path was requested.
    CancellationRequested {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Cancellation witness issued for the request.
        witness_id: AuthorityWitnessId,
        /// Owner whose lifecycle triggered the cancellation.
        owner_id: FragmentOwnerId,
        /// Ownership reason for the cancellation request.
        reason: OwnershipTerminalReason,
    },
    /// Explicit cancellation path completed.
    Cancelled {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Cancellation witness used for the completion.
        witness_id: AuthorityWitnessId,
        /// Ownership reason for the completed cancellation.
        reason: OwnershipTerminalReason,
    },
    /// Output-condition verification was evaluated at commit time.
    OutputConditionChecked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Predicate reference that was checked.
        predicate_ref: String,
        /// Optional witness reference used by the check.
        witness_ref: Option<String>,
        /// Opaque output digest checked by the verifier.
        output_digest: String,
        /// Verification outcome.
        passed: bool,
    },
}

/// The ProtocolMachine execution result for a single step.
#[derive(Debug)]
pub enum StepResult {
    /// A coroutine executed an instruction and may continue.
    Continue,
    /// No coroutines are ready (all blocked or done).
    Stuck,
    /// All coroutines have completed.
    AllDone,
}

/// Terminal status returned by bounded ProtocolMachine run APIs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RunStatus {
    /// All coroutines reached terminal states.
    AllDone,
    /// No runnable coroutines remain (blocked/stuck).
    Stuck,
    /// `max_rounds`/`max_steps` budget was exhausted before termination.
    MaxRoundsExceeded,
}

/// Debug metadata for the most recent scheduler-dispatched step.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SchedExecStatus {
    /// Instruction continued execution.
    Continue,
    /// Instruction yielded cooperative control.
    Yielded,
    /// Instruction blocked.
    Blocked,
    /// Coroutine halted normally.
    Halted,
    /// Coroutine faulted.
    Faulted,
}

/// Debug metadata for the most recent scheduler-dispatched step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SchedStepDebug {
    /// Selected coroutine id.
    pub selected_coro: usize,
    /// Instruction-step execution status.
    pub exec_status: SchedExecStatus,
}
