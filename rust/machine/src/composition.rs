//! Protocol composition API for running many protocols in one ProtocolMachine instance.
//!
//! This layer provides:
//! - proof-carrying admission (`LinkOKFull`-style certificate flag),
//! - shared immutable protocol artifacts (`Arc<CodeImage>`),
//! - memory-budget accounting for composed workloads.

use std::mem::size_of;
use std::sync::Arc;

use crate::determinism::DeterminismMode;
use crate::effect::EffectHandler;
use crate::engine::{ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError};
use crate::loader::CodeImage;
use crate::output_condition::OutputConditionPolicy;
use crate::runtime_contracts::{
    enforce_protocol_machine_runtime_gates, execution_profile_supported,
    ProtocolMachineAdmissibilityClass, ProtocolMachineEscalationWindowClass,
    ProtocolMachineExecutionProfile, ProtocolMachineFairnessAssumption, RuntimeContracts,
    RuntimeGateResult,
};
use crate::scheduler::SchedPolicy;

/// Determinism capability required to admit a protocol bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeterminismCapability {
    /// Supports full determinism for fixed initial state/policy/effect trace.
    Full,
    /// Supports determinism modulo effect traces.
    ModuloEffects,
    /// Supports determinism modulo admissible commutativity.
    ModuloCommutativity,
    /// Supports replay determinism profile.
    Replay,
}

/// Scheduler profile capability required to admit a protocol bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchedulerCapability {
    /// Cooperative scheduler profile.
    Cooperative,
    /// Round-robin scheduler profile.
    RoundRobin,
    /// Priority scheduler profile.
    Priority,
    /// Progress-aware scheduler profile.
    ProgressAware,
}

/// Theorem-pack capabilities surfaced by a proof artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoremPackCapabilities {
    /// Determinism profiles certified by the proof artifact.
    pub determinism: Vec<DeterminismCapability>,
    /// Scheduler profiles certified by the proof artifact.
    pub schedulers: Vec<SchedulerCapability>,
    /// Whether output-condition commit-gating is certified.
    pub output_condition_gating: bool,
}

impl TheoremPackCapabilities {
    /// Capability set that allows all currently supported advanced runtime modes.
    #[must_use]
    pub fn full() -> Self {
        Self {
            determinism: vec![
                DeterminismCapability::Full,
                DeterminismCapability::ModuloEffects,
                DeterminismCapability::ModuloCommutativity,
                DeterminismCapability::Replay,
            ],
            schedulers: vec![
                SchedulerCapability::Cooperative,
                SchedulerCapability::RoundRobin,
                SchedulerCapability::Priority,
                SchedulerCapability::ProgressAware,
            ],
            output_condition_gating: true,
        }
    }

    /// Proof-carrying execution profile derived from theorem-pack capabilities.
    #[must_use]
    pub fn execution_profile(&self) -> ProtocolMachineExecutionProfile {
        let mut fairness_assumptions: std::collections::BTreeSet<_> =
            [ProtocolMachineFairnessAssumption::ScheduleConfluence]
                .into_iter()
                .collect();
        if self.schedulers.iter().any(|scheduler| {
            matches!(
                scheduler,
                SchedulerCapability::RoundRobin
                    | SchedulerCapability::Priority
                    | SchedulerCapability::ProgressAware
            )
        }) {
            fairness_assumptions.insert(ProtocolMachineFairnessAssumption::StarvationFreedom);
        }
        if self
            .schedulers
            .iter()
            .any(|scheduler| matches!(scheduler, SchedulerCapability::ProgressAware))
        {
            fairness_assumptions.insert(ProtocolMachineFairnessAssumption::LivenessFairness);
        }

        let mut admissibility_classes: std::collections::BTreeSet<_> = [
            ProtocolMachineAdmissibilityClass::LocalEnvelope,
            ProtocolMachineAdmissibilityClass::ShardedEnvelope,
        ]
        .into_iter()
        .collect();
        let mut escalation_window_classes: std::collections::BTreeSet<_> =
            [ProtocolMachineEscalationWindowClass::ProgressContractBounded]
                .into_iter()
                .collect();
        if self.output_condition_gating {
            admissibility_classes.insert(ProtocolMachineAdmissibilityClass::ProtocolEnvelopeBridge);
            escalation_window_classes
                .insert(ProtocolMachineEscalationWindowClass::ProtocolBridgeBounded);
        }
        if self
            .determinism
            .iter()
            .any(|capability| !matches!(capability, DeterminismCapability::Full))
        {
            escalation_window_classes
                .insert(ProtocolMachineEscalationWindowClass::AdmissionComplexityBounded);
        }

        ProtocolMachineExecutionProfile {
            fairness_assumptions,
            admissibility_classes,
            escalation_window_classes,
            theorem_pack_eligibility: vec![
                ("protocol_machine_envelope_adherence".to_string(), true),
                (
                    "protocol_machine_envelope_admission".to_string(),
                    self.determinism.iter().any(|capability| {
                        matches!(
                            capability,
                            DeterminismCapability::Full
                                | DeterminismCapability::Replay
                                | DeterminismCapability::ModuloEffects
                                | DeterminismCapability::ModuloCommutativity
                        )
                    }),
                ),
                (
                    "protocol_envelope_bridge".to_string(),
                    self.output_condition_gating,
                ),
            ],
        }
    }
}

/// Proof/certificate artifact required for composed protocol admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompositionCertificate {
    /// Stable identifier for the certificate/proof artifact.
    pub artifact_id: String,
    /// Whether this artifact witnesses `LinkOKFull`-style compatibility.
    pub link_ok_full: bool,
    /// Theorem-pack capabilities proven by this certificate.
    pub theorem_pack: TheoremPackCapabilities,
    /// Optional runtime contract bundle required for advanced runtime modes.
    pub runtime_contracts: Option<RuntimeContracts>,
}

/// Immutable protocol bundle loaded by the composition API.
#[derive(Debug, Clone)]
pub struct ProtocolBundle {
    /// Shared immutable code image.
    pub code: Arc<CodeImage>,
    /// Certificate checked at admission time.
    pub certificate: CompositionCertificate,
}

impl ProtocolBundle {
    /// Construct a bundle from a code image and certificate.
    #[must_use]
    pub fn new(code: Arc<CodeImage>, certificate: CompositionCertificate) -> Self {
        Self { code, certificate }
    }
}

/// Memory budget policy for composed execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryBudget {
    /// Max bytes allowed per coroutine.
    pub max_bytes_per_coroutine: usize,
    /// Max bytes allowed per session.
    pub max_bytes_per_session: usize,
    /// Max incremental bytes allowed per additional protocol.
    pub max_incremental_bytes_per_protocol: usize,
}

impl Default for MemoryBudget {
    fn default() -> Self {
        Self {
            max_bytes_per_coroutine: 64 * 1024,
            max_bytes_per_session: 256 * 1024,
            max_incremental_bytes_per_protocol: 128 * 1024,
        }
    }
}

/// Composition memory usage snapshot.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MemoryUsage {
    /// Estimated bytes per coroutine.
    pub bytes_per_coroutine: usize,
    /// Estimated bytes per session.
    pub bytes_per_session: usize,
    /// Estimated incremental overhead per protocol.
    pub incremental_bytes_per_protocol: usize,
    /// Number of loaded protocol bundles.
    pub protocol_count: usize,
    /// Number of live sessions.
    pub session_count: usize,
    /// Number of live coroutines.
    pub coroutine_count: usize,
}

/// Errors emitted by the composition API.
#[derive(Debug, thiserror::Error)]
pub enum CompositionError {
    /// Missing/invalid proof artifact.
    #[error("bundle `{artifact_id}` rejected: missing LinkOKFull compatibility evidence")]
    MissingCompatibilityProof {
        /// Certificate artifact id that failed admission.
        artifact_id: String,
    },
    /// The certificate does not expose required theorem/capability evidence.
    #[error("bundle `{artifact_id}` rejected: missing required capability `{capability}`")]
    MissingCapability {
        /// Certificate artifact id that failed admission.
        artifact_id: String,
        /// Human-readable capability key.
        capability: String,
    },
    /// Advanced runtime mode requires runtime contract evidence.
    #[error("bundle `{artifact_id}` rejected: missing ProtocolMachine runtime contracts for advanced mode")]
    MissingRuntimeContracts {
        /// Certificate artifact id that failed admission.
        artifact_id: String,
    },
    /// Admission would violate memory budget.
    #[error("bundle `{artifact_id}` rejected: memory budget exceeded ({reason})")]
    BudgetExceeded {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
        /// Human-readable budget reason.
        reason: String,
    },
    /// ProtocolMachine-layer load/run failure.
    #[error(transparent)]
    Vm(#[from] ProtocolMachineError),
}

/// Runtime wrapper for composed protocol execution.
#[derive(Debug)]
pub struct ComposedRuntime {
    machine: ProtocolMachine,
    bundles: Vec<ProtocolBundle>,
    budget: MemoryBudget,
    usage: MemoryUsage,
}

impl ComposedRuntime {
    /// Create an empty composed runtime.
    #[must_use]
    pub fn new(config: ProtocolMachineConfig, budget: MemoryBudget) -> Self {
        let machine = ProtocolMachine::new(config);
        Self {
            machine,
            bundles: Vec::new(),
            budget,
            usage: MemoryUsage {
                bytes_per_coroutine: size_of::<crate::coroutine::Coroutine>(),
                bytes_per_session: size_of::<crate::session::SessionState>(),
                incremental_bytes_per_protocol: size_of::<Arc<CodeImage>>(),
                ..MemoryUsage::default()
            },
        }
    }

    /// Admit a protocol bundle after certificate + budget checks.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when proof or budget checks fail.
    pub fn admit_bundle(&mut self, bundle: ProtocolBundle) -> Result<(), CompositionError> {
        if !bundle.certificate.link_ok_full {
            return Err(CompositionError::MissingCompatibilityProof {
                artifact_id: bundle.certificate.artifact_id,
            });
        }
        self.require_capabilities(&bundle)?;

        if self.usage.incremental_bytes_per_protocol
            > self.budget.max_incremental_bytes_per_protocol
        {
            return Err(CompositionError::BudgetExceeded {
                artifact_id: bundle.certificate.artifact_id,
                reason: "incremental protocol overhead".to_string(),
            });
        }

        self.bundles.push(bundle);
        self.usage.protocol_count = self.bundles.len();
        Ok(())
    }

    /// Load one session instance from an admitted bundle index.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when index is invalid or ProtocolMachine loading fails.
    pub fn load_bundle_session(&mut self, bundle_idx: usize) -> Result<usize, CompositionError> {
        let bundle =
            self.bundles
                .get(bundle_idx)
                .ok_or_else(|| CompositionError::BudgetExceeded {
                    artifact_id: format!("bundle/{bundle_idx}"),
                    reason: "bundle index out of range".to_string(),
                })?;

        let sid = self.machine.load_choreography(&bundle.code)?;
        self.refresh_usage();
        self.assert_budget(bundle_idx)?;
        Ok(sid)
    }

    /// Load `sessions` instances from a bundle index.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when any session load fails.
    pub fn load_bundle_sessions(
        &mut self,
        bundle_idx: usize,
        sessions: usize,
    ) -> Result<Vec<usize>, CompositionError> {
        let mut out = Vec::with_capacity(sessions);
        for _ in 0..sessions {
            out.push(self.load_bundle_session(bundle_idx)?);
        }
        Ok(out)
    }

    /// Run the composed runtime.
    ///
    /// # Errors
    ///
    /// Returns ProtocolMachine-layer errors as composition errors.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_steps: usize,
    ) -> Result<(), CompositionError> {
        self.machine.run(handler, max_steps)?;
        self.refresh_usage();
        Ok(())
    }

    /// Access current memory usage snapshot.
    #[must_use]
    pub fn memory_usage(&self) -> &MemoryUsage {
        &self.usage
    }

    /// Access admitted bundles.
    #[must_use]
    pub fn bundles(&self) -> &[ProtocolBundle] {
        &self.bundles
    }

    /// Access underlying ProtocolMachine.
    #[must_use]
    pub fn machine(&self) -> &ProtocolMachine {
        &self.machine
    }

    fn refresh_usage(&mut self) {
        self.usage.session_count = self.machine.session_count();
        self.usage.coroutine_count = self.machine.coroutine_count();
        self.usage.protocol_count = self.bundles.len();
    }

    fn assert_budget(&self, bundle_idx: usize) -> Result<(), CompositionError> {
        let per_coro = self.usage.bytes_per_coroutine;
        let per_sess = self.usage.bytes_per_session;
        let artifact_id = self
            .bundles
            .get(bundle_idx)
            .map(|b| b.certificate.artifact_id.clone())
            .unwrap_or_else(|| format!("bundle/{bundle_idx}"));
        if per_coro > self.budget.max_bytes_per_coroutine {
            return Err(CompositionError::BudgetExceeded {
                artifact_id,
                reason: "bytes_per_coroutine".to_string(),
            });
        }
        if per_sess > self.budget.max_bytes_per_session {
            return Err(CompositionError::BudgetExceeded {
                artifact_id,
                reason: "bytes_per_session".to_string(),
            });
        }
        Ok(())
    }

    fn require_capabilities(&self, bundle: &ProtocolBundle) -> Result<(), CompositionError> {
        let cert = &bundle.certificate;
        let caps = &cert.theorem_pack;
        let runtime_contracts = cert.runtime_contracts.as_ref();

        match enforce_protocol_machine_runtime_gates(self.machine.config(), runtime_contracts) {
            RuntimeGateResult::Admitted => {}
            RuntimeGateResult::RejectedMissingContracts => {
                return Err(CompositionError::MissingRuntimeContracts {
                    artifact_id: cert.artifact_id.clone(),
                });
            }
            RuntimeGateResult::RejectedUnsupportedDeterminismProfile => {
                return Err(CompositionError::MissingCapability {
                    artifact_id: cert.artifact_id.clone(),
                    capability: format!(
                        "determinism_profile::{:?}",
                        self.machine.config().determinism_mode
                    ),
                });
            }
        }

        let required_sched = match self.machine.config().sched_policy {
            SchedPolicy::Cooperative => SchedulerCapability::Cooperative,
            SchedPolicy::RoundRobin => SchedulerCapability::RoundRobin,
            SchedPolicy::Priority(_) => SchedulerCapability::Priority,
            SchedPolicy::ProgressAware => SchedulerCapability::ProgressAware,
        };
        if !caps.schedulers.contains(&required_sched) {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: format!("scheduler::{required_sched:?}"),
            });
        }

        let required_det = match self.machine.config().determinism_mode {
            DeterminismMode::Full => DeterminismCapability::Full,
            DeterminismMode::ModuloEffects => DeterminismCapability::ModuloEffects,
            DeterminismMode::ModuloCommutativity => DeterminismCapability::ModuloCommutativity,
            DeterminismMode::Replay => DeterminismCapability::Replay,
        };
        if !caps.determinism.contains(&required_det) {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: format!("determinism::{required_det:?}"),
            });
        }
        if !execution_profile_supported(
            &caps.execution_profile(),
            self.machine.config(),
            runtime_contracts,
        ) {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: "execution_profile".to_string(),
            });
        }
        if !matches!(
            self.machine.config().output_condition_policy,
            OutputConditionPolicy::Disabled
        ) && !caps.output_condition_gating
        {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: "output_condition_gating".to_string(),
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use telltale_types::{GlobalType, Label, LocalTypeR};

    use super::*;
    use crate::coroutine::Value;
    use crate::effect::{EffectFailure, EffectResult};

    #[derive(Debug, Clone, Copy)]
    struct Noop;

    impl EffectHandler for Noop {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Str(label.to_string()))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> EffectResult<()> {
            EffectResult::success(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> EffectResult<String> {
            match labels.first().cloned() {
                Some(label) => EffectResult::success(label),
                None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
            }
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }
    }

    fn image(label: &str) -> Arc<CodeImage> {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new(label), LocalTypeR::End),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new(label), LocalTypeR::End),
        );
        let global = GlobalType::send("A", "B", Label::new(label), GlobalType::End);
        Arc::new(CodeImage::from_local_types(&local_types, &global))
    }

    #[test]
    fn proof_carrying_admission_rejects_missing_link_ok_full() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let bad = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/bad".to_string(),
                link_ok_full: false,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        assert!(matches!(
            runtime.admit_bundle(bad),
            Err(CompositionError::MissingCompatibilityProof { .. })
        ));
    }

    #[test]
    fn immutable_code_artifacts_are_arc_shared() {
        let shared = image("m");
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let b1 = ProtocolBundle::new(
            Arc::clone(&shared),
            CompositionCertificate {
                artifact_id: "cert/1".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        let b2 = ProtocolBundle::new(
            Arc::clone(&shared),
            CompositionCertificate {
                artifact_id: "cert/2".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        runtime.admit_bundle(b1).expect("admit b1");
        runtime.admit_bundle(b2).expect("admit b2");
        assert!(
            Arc::strong_count(&shared) >= 3,
            "bundle admission should keep shared immutable artifacts in Arc"
        );
    }

    #[test]
    fn composed_execution_runs_and_usage_grows_monotonically() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let b = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/ok".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        runtime.admit_bundle(b).expect("admit");
        runtime
            .load_bundle_sessions(0, 8)
            .expect("load composed sessions");
        let usage_before = runtime.memory_usage().clone();
        assert!(usage_before.session_count >= 8);
        assert!(usage_before.coroutine_count >= 16);
        runtime.run(&Noop, 512).expect("composed run");
        let usage_after = runtime.memory_usage().clone();
        assert!(usage_after.session_count >= usage_before.session_count);
        assert!(usage_after.coroutine_count >= usage_before.coroutine_count);
    }

    #[test]
    fn admission_rejects_missing_scheduler_profile_capability() {
        let cfg = ProtocolMachineConfig {
            sched_policy: SchedPolicy::ProgressAware,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-sched".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![SchedulerCapability::Cooperative],
                    output_condition_gating: true,
                },
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );

        let err = runtime
            .admit_bundle(bundle)
            .expect_err("should reject bundle");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "scheduler::ProgressAware"
        ));
    }

    #[test]
    fn admission_rejects_missing_determinism_capability() {
        let cfg = ProtocolMachineConfig {
            determinism_mode: DeterminismMode::ModuloCommutativity,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-det".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![SchedulerCapability::Cooperative],
                    output_condition_gating: true,
                },
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );

        let err = runtime
            .admit_bundle(bundle)
            .expect_err("should reject bundle");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "determinism::ModuloCommutativity"
        ));
    }

    #[test]
    fn admission_rejects_missing_output_condition_capability() {
        let cfg = ProtocolMachineConfig {
            output_condition_policy: OutputConditionPolicy::AllowAll,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-output-gate".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![SchedulerCapability::Cooperative],
                    output_condition_gating: false,
                },
                runtime_contracts: None,
            },
        );

        let err = runtime
            .admit_bundle(bundle)
            .expect_err("should reject bundle");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "execution_profile"
        ));
    }

    #[test]
    fn admission_accepts_when_required_capabilities_present() {
        let cfg = ProtocolMachineConfig {
            sched_policy: SchedPolicy::RoundRobin,
            determinism_mode: DeterminismMode::ModuloEffects,
            output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
                "machine.observable_output".to_string(),
            ]),
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/full".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("bundle should be admitted");
    }

    #[test]
    fn admission_accepts_minimal_required_capabilities_without_full_parity() {
        let cfg = ProtocolMachineConfig::default();
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/minimal-required".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![
                        SchedulerCapability::Cooperative,
                        SchedulerCapability::ProgressAware,
                    ],
                    output_condition_gating: true,
                },
                runtime_contracts: None,
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("minimal required capabilities should be sufficient");
    }

    #[test]
    fn admission_rejects_advanced_mode_without_runtime_contracts() {
        let cfg = ProtocolMachineConfig {
            sched_policy: SchedPolicy::RoundRobin,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-runtime-contracts".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        let err = runtime
            .admit_bundle(bundle)
            .expect_err("advanced mode should reject missing runtime contracts");
        assert!(matches!(
            err,
            CompositionError::MissingRuntimeContracts { .. }
        ));
    }

    #[test]
    fn admission_rejects_replay_profile_without_mixed_profile_gate() {
        let cfg = ProtocolMachineConfig {
            determinism_mode: DeterminismMode::Replay,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let mut contracts = RuntimeContracts::full();
        contracts.can_use_mixed_determinism_profiles = false;
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-mixed-profile-gate".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(contracts),
            },
        );
        let err = runtime
            .admit_bundle(bundle)
            .expect_err("replay profile should require mixed-profile gate");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "determinism_profile::Replay"
        ));
    }

    #[test]
    fn admission_accepts_replay_profile_with_contracts_and_capability() {
        let cfg = ProtocolMachineConfig {
            determinism_mode: DeterminismMode::Replay,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/replay-ok".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("replay profile should admit with matching contracts");
    }
}
