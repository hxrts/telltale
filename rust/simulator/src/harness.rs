//! High-level simulator harness for third-party integration.
//!
//! This module wraps low-level runner entrypoints with a stable host-adapter
//! interface, generated effect-family scenario support, and config-file workflow.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use telltale_types::{FixedQ32, GlobalType, LocalTypeR};

use crate::contracts::{assert_contracts, ContractCheckConfig};
use crate::material::MaterialModel;
use crate::runner::{run_with_scenario, ScenarioResult};
use crate::scenario::{ResolvedTheoremProfile, Scenario};
use crate::EffectHandler;

/// Host integration hook for simulator execution.
pub trait HostAdapter {
    /// Return the external handler implementation used for protocol-machine execution.
    fn effect_handler(&self) -> &dyn EffectHandler;

    /// Optionally provide initial role state vectors.
    ///
    /// Returning `None` delegates initial state derivation to the harness.
    fn initial_states(
        &self,
        _scenario: &Scenario,
    ) -> Result<Option<BTreeMap<String, Vec<FixedQ32>>>, String> {
        Ok(None)
    }

    /// Optional post-run validation hook.
    ///
    /// # Errors
    ///
    /// Return an error to reject the run result.
    fn validate_result(
        &self,
        _scenario: &Scenario,
        _result: &ScenarioResult,
    ) -> Result<(), String> {
        Ok(())
    }
}

/// Thin adapter that wraps an external handler reference directly.
pub struct DirectAdapter<'a> {
    handler: &'a dyn EffectHandler,
}

impl<'a> DirectAdapter<'a> {
    /// Create a direct adapter from an existing effect handler.
    #[must_use]
    pub fn new(handler: &'a dyn EffectHandler) -> Self {
        Self { handler }
    }
}

impl HostAdapter for DirectAdapter<'_> {
    fn effect_handler(&self) -> &dyn EffectHandler {
        self.handler
    }
}

/// Adapter that uses material-derived handlers from scenario params.
pub struct MaterialAdapter {
    model: Box<dyn MaterialModel>,
    handler: Box<dyn EffectHandler>,
}

impl MaterialAdapter {
    /// Build a material adapter from any material-model implementation.
    #[must_use]
    pub fn new<M>(model: M) -> Self
    where
        M: MaterialModel + 'static,
    {
        Self::from_boxed_model(Box::new(model))
    }

    /// Build a material adapter from a boxed material-model implementation.
    #[must_use]
    pub fn from_boxed_model(model: Box<dyn MaterialModel>) -> Self {
        let handler = crate::handler_from_model(model.as_ref());
        Self { model, handler }
    }

    /// Build a material adapter from a scenario.
    ///
    /// # Errors
    ///
    /// Returns an error when the scenario does not declare built-in material params.
    pub fn from_scenario(scenario: &Scenario) -> Result<Self, String> {
        let material = scenario
            .material
            .clone()
            .ok_or_else(|| "scenario is missing built-in material parameters".to_string())?;
        Ok(Self::new(material))
    }
}

impl HostAdapter for MaterialAdapter {
    fn effect_handler(&self) -> &dyn EffectHandler {
        self.handler.as_ref()
    }

    fn initial_states(
        &self,
        scenario: &Scenario,
    ) -> Result<Option<BTreeMap<String, Vec<FixedQ32>>>, String> {
        derive_initial_states_for_model(self.model.as_ref(), &scenario.roles).map(Some)
    }
}

/// Input specification for one harness run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HarnessSpec {
    /// Local types keyed by role name.
    pub local_types: BTreeMap<String, LocalTypeR>,
    /// Global type for the loaded choreography.
    pub global_type: GlobalType,
    /// Scenario with middleware and monitoring settings.
    pub scenario: Scenario,
    /// Optional explicit initial states keyed by role.
    #[serde(default)]
    pub initial_states: BTreeMap<String, Vec<FixedQ32>>,
}

impl HarnessSpec {
    /// Construct a spec without explicit initial state overrides.
    #[must_use]
    pub fn new(
        local_types: BTreeMap<String, LocalTypeR>,
        global_type: GlobalType,
        scenario: Scenario,
    ) -> Self {
        Self {
            local_types,
            global_type,
            scenario,
            initial_states: BTreeMap::new(),
        }
    }

    /// Override initial states.
    #[must_use]
    pub fn with_initial_states(mut self, initial_states: BTreeMap<String, Vec<FixedQ32>>) -> Self {
        self.initial_states = initial_states;
        self
    }
}

/// Serialized single-file harness config.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HarnessConfig {
    /// Run specification.
    #[serde(flatten)]
    pub spec: HarnessSpec,
    /// Optional contract checks evaluated after run.
    #[serde(default)]
    pub contracts: ContractCheckConfig,
}

/// Batch execution configuration for harness runs.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize)]
pub struct BatchConfig {
    /// Optional worker count override.
    ///
    /// When absent, the harness resolves a CI-aware default.
    #[serde(default)]
    pub parallelism: Option<usize>,
}

/// Deterministic batch execution result.
pub struct BatchRunResult {
    /// Resolved worker count.
    pub parallelism: usize,
    /// Resolved theorem/profile manifest for the batch inputs.
    pub manifest: BatchRunManifest,
    /// Per-spec results in the same order as the input slice.
    pub results: Vec<Result<ScenarioResult, String>>,
}

/// Resolved theorem/profile manifest for one batch execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchRunManifest {
    /// Resolved worker count.
    pub parallelism: usize,
    /// Per-spec theorem/profile resolution in input order.
    pub runs: Vec<BatchRunManifestEntry>,
}

/// One batch manifest entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchRunManifestEntry {
    /// Scenario name.
    pub scenario_name: String,
    /// Resolved theorem/profile data when execution resolution succeeded.
    pub theorem_profile: Option<ResolvedTheoremProfile>,
    /// Resolution error when execution settings could not be resolved.
    pub theorem_profile_error: Option<String>,
}

impl HarnessConfig {
    /// Load harness config from JSON or TOML.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or parsed.
    pub fn from_file(path: &Path) -> Result<Self, String> {
        let content =
            std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;

        match path.extension().and_then(std::ffi::OsStr::to_str) {
            Some("json") => {
                serde_json::from_str(&content).map_err(|e| format!("parse JSON config: {e}"))
            }
            Some("toml") => toml::from_str(&content).map_err(|e| format!("parse TOML config: {e}")),
            _ => serde_json::from_str(&content)
                .or_else(|_| toml::from_str(&content))
                .map_err(|_| {
                    format!(
                        "parse config {}: unsupported extension, expected .json or .toml",
                        path.display()
                    )
                }),
        }
    }
}

/// High-level harness runner.
pub struct SimulationHarness<'a, A: HostAdapter + ?Sized> {
    adapter: &'a A,
}

impl<'a, A: HostAdapter + ?Sized> SimulationHarness<'a, A> {
    /// Create a harness for one host adapter.
    #[must_use]
    pub fn new(adapter: &'a A) -> Self {
        Self { adapter }
    }

    /// Execute a spec through `run_with_scenario` and adapter hooks.
    ///
    /// # Errors
    ///
    /// Returns an error when setup, protocol-machine execution, or adapter validation fails.
    pub fn run(&self, spec: &HarnessSpec) -> Result<ScenarioResult, String> {
        let initial_states = resolve_initial_states(spec, self.adapter)?;

        let result = run_with_scenario(
            &spec.local_types,
            &spec.global_type,
            &initial_states,
            &spec.scenario,
            self.adapter.effect_handler(),
        )?;

        self.adapter.validate_result(&spec.scenario, &result)?;
        Ok(result)
    }

    /// Execute a config and enforce declared contract checks.
    ///
    /// # Errors
    ///
    /// Returns an error when run execution fails or contract checks fail.
    pub fn run_config(&self, config: &HarnessConfig) -> Result<ScenarioResult, String> {
        let result = self.run(&config.spec)?;
        assert_contracts(&result, &config.contracts)?;
        Ok(result)
    }

    /// Execute many specs with deterministic input-order results.
    ///
    /// # Errors
    ///
    /// Returns a per-spec `Err` entry when one run fails.
    pub fn run_batch(&self, specs: &[HarnessSpec]) -> BatchRunResult
    where
        A: Sync,
    {
        self.run_batch_with(specs, BatchConfig::default())
    }

    /// Execute many specs with explicit batch configuration.
    #[allow(clippy::missing_panics_doc)]
    pub fn run_batch_with(&self, specs: &[HarnessSpec], config: BatchConfig) -> BatchRunResult
    where
        A: Sync,
    {
        let parallelism = resolve_batch_parallelism(config.parallelism);
        let manifest = build_batch_manifest(specs, parallelism);
        if specs.is_empty() {
            return BatchRunResult {
                parallelism,
                manifest,
                results: Vec::new(),
            };
        }
        if parallelism <= 1 || specs.len() == 1 {
            return BatchRunResult {
                parallelism,
                manifest,
                results: specs.iter().map(|spec| self.run(spec)).collect(),
            };
        }

        let next = AtomicUsize::new(0);
        let (tx, rx) = std::sync::mpsc::channel();

        std::thread::scope(|scope| {
            for _ in 0..parallelism {
                let tx = tx.clone();
                let next = &next;
                scope.spawn(move || {
                    loop {
                        let idx = next.fetch_add(1, Ordering::Relaxed);
                        let Some(spec) = specs.get(idx) else {
                            break;
                        };
                        let result = self.run(spec);
                        if tx.send((idx, result)).is_err() {
                            break;
                        }
                    }
                });
            }
        });
        drop(tx);

        let mut ordered = (0..specs.len()).map(|_| None).collect::<Vec<_>>();
        for (idx, result) in rx {
            ordered[idx] = Some(result);
        }

        BatchRunResult {
            parallelism,
            manifest,
            results: ordered
                .into_iter()
                .map(|entry| {
                    entry.unwrap_or_else(|| Err("batch worker terminated without a result".into()))
                })
                .collect(),
        }
    }
}

fn build_batch_manifest(specs: &[HarnessSpec], parallelism: usize) -> BatchRunManifest {
    BatchRunManifest {
        parallelism,
        runs: specs
            .iter()
            .map(|spec| match spec.scenario.resolved_execution() {
                Ok(execution) => BatchRunManifestEntry {
                    scenario_name: spec.scenario.name.clone(),
                    theorem_profile: Some(spec.scenario.resolve_theorem_profile_for(&execution)),
                    theorem_profile_error: None,
                },
                Err(error) => BatchRunManifestEntry {
                    scenario_name: spec.scenario.name.clone(),
                    theorem_profile: None,
                    theorem_profile_error: Some(error),
                },
            })
            .collect(),
    }
}

fn resolve_initial_states<A: HostAdapter + ?Sized>(
    spec: &HarnessSpec,
    adapter: &A,
) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
    if !spec.initial_states.is_empty() {
        return Ok(spec.initial_states.clone());
    }

    if let Some(from_adapter) = adapter.initial_states(&spec.scenario)? {
        return Ok(from_adapter);
    }

    derive_initial_states(&spec.scenario)
}

/// Derive per-role initial states from material parameters.
///
/// # Errors
///
/// Returns an error when material parameters do not match scenario roles.
pub fn derive_initial_states_for_model(
    material: &dyn MaterialModel,
    roles: &[String],
) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
    material.derive_initial_states(roles)
}

fn resolve_batch_parallelism(requested: Option<usize>) -> usize {
    resolve_batch_parallelism_for(
        requested,
        running_in_ci(),
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
            .max(1),
    )
}

fn resolve_batch_parallelism_for(
    requested: Option<usize>,
    ci: bool,
    available_parallelism: usize,
) -> usize {
    match requested {
        Some(n) => n.max(1),
        None if ci => 1,
        None => available_parallelism.max(1),
    }
}

fn running_in_ci() -> bool {
    std::env::var("CI")
        .ok()
        .map(|value| {
            let normalized = value.trim().to_ascii_lowercase();
            !(normalized.is_empty() || normalized == "0" || normalized == "false")
        })
        .unwrap_or(false)
}

/// Derive per-role initial states from built-in scenario material parameters.
///
/// # Errors
///
/// Returns an error when material parameters do not match scenario roles.
pub fn derive_initial_states(
    scenario: &Scenario,
) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
    let material = scenario
        .material
        .as_ref()
        .ok_or_else(|| "scenario is missing built-in material parameters".to_string())?;
    derive_initial_states_for_model(material, &scenario.roles)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contracts::ContractCheckConfig;
    use crate::material::{HamiltonianParams, MaterialParams, MeanFieldParams};
    use telltale_machine::coroutine::Value;
    use telltale_machine::model::effects::{EffectResult, SendDecision, SendDecisionInput};

    struct DummyHandler;

    impl EffectHandler for DummyHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Unit)
        }

        fn send_decision(&self, _input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
            EffectResult::success(SendDecision::Deliver(Value::Unit))
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
            EffectResult::success(labels.first().cloned().unwrap_or_default())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }
    }

    struct DummyMaterialModel;

    impl MaterialModel for DummyMaterialModel {
        fn layer_name(&self) -> &'static str {
            "dummy"
        }

        fn build_handler(&self) -> Box<dyn EffectHandler> {
            Box::new(DummyHandler)
        }

        fn derive_initial_states(
            &self,
            roles: &[String],
        ) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
            Ok(roles
                .iter()
                .cloned()
                .enumerate()
                .map(|(idx, role)| {
                    let idx = i64::try_from(idx).expect("index fits in i64");
                    (
                        role,
                        vec![FixedQ32::from_ratio(idx + 1, 1).expect("representable")],
                    )
                })
                .collect())
        }
    }

    fn mean_field_scenario() -> Scenario {
        Scenario {
            name: "mean_field_harness".to_string(),
            roles: vec!["A".to_string(), "B".to_string()],
            steps: 8,
            execution: crate::scenario::ExecutionSpec::default(),
            seed: 7,
            network: None,
            material: Some(MaterialParams::MeanField(MeanFieldParams {
                beta: FixedQ32::one(),
                species: vec!["up".into(), "down".into()],
                initial_state: vec![FixedQ32::half(), FixedQ32::half()],
                step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
            })),
            events: Vec::new(),
            properties: None,
            checkpoint_interval: None,
            theorem: crate::scenario::TheoremProfileSpec::default(),
        }
    }

    #[test]
    fn derive_initial_states_for_mean_field_broadcasts_state() {
        let scenario = mean_field_scenario();
        let states = derive_initial_states(&scenario).expect("derive states");
        assert_eq!(states.len(), 2);
        assert_eq!(states["A"], vec![FixedQ32::half(), FixedQ32::half()]);
        assert_eq!(states["B"], vec![FixedQ32::half(), FixedQ32::half()]);
    }

    #[test]
    fn derive_initial_states_for_hamiltonian_maps_role_index() {
        let mut scenario = mean_field_scenario();
        scenario.material = Some(MaterialParams::Hamiltonian(HamiltonianParams {
            spring_constant: FixedQ32::one(),
            mass: FixedQ32::one(),
            dimensions: 1,
            initial_positions: vec![FixedQ32::one(), FixedQ32::neg_one()],
            initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        }));

        let states = derive_initial_states(&scenario).expect("derive states");
        assert_eq!(states["A"], vec![FixedQ32::one(), FixedQ32::zero()]);
        assert_eq!(states["B"], vec![FixedQ32::neg_one(), FixedQ32::zero()]);
    }

    #[test]
    fn material_adapter_supports_custom_material_models() {
        let scenario = mean_field_scenario();
        let adapter = MaterialAdapter::new(DummyMaterialModel);
        let states = adapter
            .initial_states(&scenario)
            .expect("derive states")
            .expect("adapter provides states");

        assert_eq!(states["A"], vec![FixedQ32::one()]);
        assert_eq!(states["B"], vec![FixedQ32::from_ratio(2, 1).expect("2")]);
        adapter.effect_handler();
    }

    #[test]
    fn material_adapter_from_scenario_requires_material() {
        let mut scenario = mean_field_scenario();
        scenario.material = None;
        let err = match MaterialAdapter::from_scenario(&scenario) {
            Ok(_) => panic!("material should be required"),
            Err(err) => err,
        };
        assert!(err.contains("missing built-in material"));
    }

    #[test]
    fn derive_initial_states_requires_material_when_not_provided_by_adapter() {
        let mut scenario = mean_field_scenario();
        scenario.material = None;
        let err = derive_initial_states(&scenario).expect_err("material should be required");
        assert!(err.contains("missing built-in material"));
    }

    #[test]
    fn config_default_contracts_enable_core_checks() {
        let config = HarnessConfig {
            spec: HarnessSpec::new(BTreeMap::new(), GlobalType::End, mean_field_scenario()),
            contracts: ContractCheckConfig::default(),
        };

        assert!(config.contracts.no_property_violations);
        assert!(config.contracts.replay_coherence);
    }

    #[test]
    fn harness_config_from_json_file_roundtrip() {
        let config = HarnessConfig {
            spec: HarnessSpec::new(BTreeMap::new(), GlobalType::End, mean_field_scenario()),
            contracts: ContractCheckConfig::default(),
        };

        let path = std::env::temp_dir().join(format!(
            "telltale_sim_harness_{}_{}.json",
            std::process::id(),
            config.spec.scenario.seed
        ));
        let payload = serde_json::to_string(&config).expect("serialize config");
        std::fs::write(&path, payload).expect("write config");

        let loaded = HarnessConfig::from_file(&path).expect("load config");
        std::fs::remove_file(&path).expect("remove config");

        assert_eq!(loaded.spec.scenario.name, config.spec.scenario.name);
        assert_eq!(
            loaded.contracts.replay_coherence,
            config.contracts.replay_coherence
        );
    }

    #[test]
    fn batch_parallelism_serializes_in_ci() {
        assert_eq!(resolve_batch_parallelism_for(Some(4), true, 8), 4);
        assert_eq!(resolve_batch_parallelism_for(None, true, 8), 1);
        assert_eq!(resolve_batch_parallelism_for(None, false, 8), 8);
    }

    #[test]
    fn run_batch_preserves_input_order() {
        let scenario_a = mean_field_scenario();
        let mut scenario_b = mean_field_scenario();
        scenario_b.seed = 99;

        let local_types = BTreeMap::from([
            ("A".to_string(), LocalTypeR::End),
            ("B".to_string(), LocalTypeR::End),
        ]);
        let spec_a = HarnessSpec::new(local_types.clone(), GlobalType::End, scenario_a);
        let spec_b = HarnessSpec::new(local_types, GlobalType::End, scenario_b);

        let adapter = MaterialAdapter::from_scenario(&spec_a.scenario).expect("material adapter");
        let harness = SimulationHarness::new(&adapter);
        let batch = harness.run_batch_with(&[spec_a, spec_b], BatchConfig { parallelism: Some(2) });

        assert_eq!(batch.parallelism, 2);
        assert_eq!(batch.manifest.parallelism, 2);
        assert_eq!(batch.results.len(), 2);
        assert_eq!(batch.manifest.runs.len(), 2);
        let first = batch.results[0].as_ref().expect("first result");
        let second = batch.results[1].as_ref().expect("second result");
        assert_eq!(first.stats.seed, 7);
        assert_eq!(second.stats.seed, 99);
        assert_eq!(
            batch.manifest.runs[0]
                .theorem_profile
                .as_ref()
                .expect("first theorem profile"),
            &first.stats.theorem_profile
        );
        assert_eq!(
            batch.manifest.runs[1]
                .theorem_profile
                .as_ref()
                .expect("second theorem profile"),
            &second.stats.theorem_profile
        );
    }
}
