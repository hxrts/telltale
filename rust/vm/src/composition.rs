//! Protocol composition API for running many protocols in one VM instance.
//!
//! This layer provides:
//! - proof-carrying admission (`LinkOKFull`-style certificate flag),
//! - shared immutable protocol artifacts (`Arc<CodeImage>`),
//! - memory-budget accounting for composed workloads.

use std::mem::size_of;
use std::sync::Arc;

use crate::determinism::DeterminismMode;
use crate::effect::EffectHandler;
use crate::loader::CodeImage;
use crate::output_condition::OutputConditionPolicy;
use crate::scheduler::SchedPolicy;
use crate::vm::{VMConfig, VMError, VM};

/// Determinism capability required to admit a protocol bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeterminismCapability {
    /// Supports full determinism for fixed initial state/policy/effect trace.
    Full,
    /// Supports determinism modulo effect traces.
    ModuloEffects,
    /// Supports determinism modulo admissible commutativity.
    ModuloCommutativity,
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
    /// Admission would violate memory budget.
    #[error("bundle `{artifact_id}` rejected: memory budget exceeded ({reason})")]
    BudgetExceeded {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
        /// Human-readable budget reason.
        reason: String,
    },
    /// VM-layer load/run failure.
    #[error(transparent)]
    Vm(#[from] VMError),
}

/// Runtime wrapper for composed protocol execution.
#[derive(Debug)]
pub struct ComposedRuntime {
    vm: VM,
    bundles: Vec<ProtocolBundle>,
    budget: MemoryBudget,
    usage: MemoryUsage,
}

impl ComposedRuntime {
    /// Create an empty composed runtime.
    #[must_use]
    pub fn new(config: VMConfig, budget: MemoryBudget) -> Self {
        let vm = VM::new(config);
        Self {
            vm,
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
    /// Returns a `CompositionError` when index is invalid or VM loading fails.
    pub fn load_bundle_session(&mut self, bundle_idx: usize) -> Result<usize, CompositionError> {
        let bundle =
            self.bundles
                .get(bundle_idx)
                .ok_or_else(|| CompositionError::BudgetExceeded {
                    artifact_id: format!("bundle/{bundle_idx}"),
                    reason: "bundle index out of range".to_string(),
                })?;

        let sid = self.vm.load_choreography(&bundle.code)?;
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
    /// Returns VM-layer errors as composition errors.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_steps: usize,
    ) -> Result<(), CompositionError> {
        self.vm.run(handler, max_steps)?;
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

    /// Access underlying VM.
    #[must_use]
    pub fn vm(&self) -> &VM {
        &self.vm
    }

    fn refresh_usage(&mut self) {
        self.usage.session_count = self.vm.session_count();
        self.usage.coroutine_count = self.vm.coroutine_count();
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

        let required_sched = match self.vm.config().sched_policy {
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

        let required_det = match self.vm.config().determinism_mode {
            DeterminismMode::Full => DeterminismCapability::Full,
            DeterminismMode::ModuloEffects => DeterminismCapability::ModuloEffects,
            DeterminismMode::ModuloCommutativity => DeterminismCapability::ModuloCommutativity,
        };
        if !caps.determinism.contains(&required_det) {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: format!("determinism::{required_det:?}"),
            });
        }

        if !matches!(
            self.vm.config().output_condition_policy,
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

    #[derive(Debug, Clone, Copy)]
    struct Noop;

    impl EffectHandler for Noop {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Label(label.to_string()))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
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
        let mut runtime = ComposedRuntime::new(VMConfig::default(), MemoryBudget::default());
        let bad = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/bad".to_string(),
                link_ok_full: false,
                theorem_pack: TheoremPackCapabilities::full(),
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
        let mut runtime = ComposedRuntime::new(VMConfig::default(), MemoryBudget::default());
        let b1 = ProtocolBundle::new(
            Arc::clone(&shared),
            CompositionCertificate {
                artifact_id: "cert/1".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
            },
        );
        let b2 = ProtocolBundle::new(
            Arc::clone(&shared),
            CompositionCertificate {
                artifact_id: "cert/2".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
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
        let mut runtime = ComposedRuntime::new(VMConfig::default(), MemoryBudget::default());
        let b = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/ok".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
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
        let cfg = VMConfig {
            sched_policy: SchedPolicy::ProgressAware,
            ..VMConfig::default()
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
        let cfg = VMConfig {
            determinism_mode: DeterminismMode::ModuloCommutativity,
            ..VMConfig::default()
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
        let cfg = VMConfig {
            output_condition_policy: OutputConditionPolicy::AllowAll,
            ..VMConfig::default()
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
            },
        );

        let err = runtime
            .admit_bundle(bundle)
            .expect_err("should reject bundle");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "output_condition_gating"
        ));
    }

    #[test]
    fn admission_accepts_when_required_capabilities_present() {
        let cfg = VMConfig {
            sched_policy: SchedPolicy::RoundRobin,
            determinism_mode: DeterminismMode::ModuloEffects,
            output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
                "vm.observable_output".to_string(),
            ]),
            ..VMConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/full".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("bundle should be admitted");
    }

    #[test]
    fn admission_accepts_minimal_required_capabilities_without_full_parity() {
        let cfg = VMConfig::default();
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/minimal-required".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![SchedulerCapability::Cooperative],
                    output_condition_gating: true,
                },
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("minimal required capabilities should be sufficient");
    }
}
