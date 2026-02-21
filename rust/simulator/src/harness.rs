//! High-level simulator harness for third-party integration.
//!
//! This module wraps low-level runner entrypoints with a stable host-adapter
//! interface and config-file workflow.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;
use telltale_types::{FixedQ32, GlobalType, LocalTypeR};

use crate::contracts::{assert_contracts, ContractCheckConfig};
use crate::material::MaterialParams;
use crate::runner::{run_with_scenario, ScenarioResult};
use crate::scenario::Scenario;
use crate::EffectHandler;

/// Host integration hook for simulator execution.
pub trait HostAdapter {
    /// Return the VM effect handler implementation used for execution.
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

/// Thin adapter that wraps a raw `EffectHandler` reference.
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
    handler: Box<dyn EffectHandler>,
}

impl MaterialAdapter {
    /// Build a material adapter from a scenario.
    #[must_use]
    pub fn from_scenario(scenario: &Scenario) -> Self {
        Self {
            handler: crate::handler_from_material(&scenario.material),
        }
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
        derive_initial_states(scenario).map(Some)
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
    /// Returns an error when setup, VM run, or adapter validation fails.
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
pub fn derive_initial_states(
    scenario: &Scenario,
) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
    let mut states = BTreeMap::new();

    match &scenario.material {
        MaterialParams::MeanField(params) => {
            if params.initial_state.is_empty() {
                return Err("mean_field material requires at least one state component".into());
            }
            for role in &scenario.roles {
                states.insert(role.clone(), params.initial_state.clone());
            }
        }
        MaterialParams::Hamiltonian(params) => {
            let n = scenario.roles.len();
            if params.initial_positions.len() < n || params.initial_momenta.len() < n {
                return Err(format!(
                    "hamiltonian material requires at least {n} positions and momenta"
                ));
            }
            for (idx, role) in scenario.roles.iter().enumerate() {
                states.insert(
                    role.clone(),
                    vec![params.initial_positions[idx], params.initial_momenta[idx]],
                );
            }
        }
        MaterialParams::ContinuumField(params) => {
            let n = scenario.roles.len();
            if params.initial_fields.len() < n {
                return Err(format!(
                    "continuum_field material requires at least {n} initial field values"
                ));
            }
            for (idx, role) in scenario.roles.iter().enumerate() {
                states.insert(role.clone(), vec![params.initial_fields[idx]]);
            }
        }
    }

    Ok(states)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contracts::ContractCheckConfig;
    use crate::material::{HamiltonianParams, MeanFieldParams};

    fn mean_field_scenario() -> Scenario {
        Scenario {
            name: "mean_field_harness".to_string(),
            roles: vec!["A".to_string(), "B".to_string()],
            steps: 8,
            concurrency: 1,
            seed: 7,
            network: None,
            material: MaterialParams::MeanField(MeanFieldParams {
                beta: FixedQ32::one(),
                species: vec!["up".into(), "down".into()],
                initial_state: vec![FixedQ32::half(), FixedQ32::half()],
                step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
            }),
            events: Vec::new(),
            properties: None,
            checkpoint_interval: None,
            output: crate::scenario::OutputConfig::default(),
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
        scenario.material = MaterialParams::Hamiltonian(HamiltonianParams {
            spring_constant: FixedQ32::one(),
            mass: FixedQ32::one(),
            dimensions: 1,
            initial_positions: vec![FixedQ32::one(), FixedQ32::neg_one()],
            initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        });

        let states = derive_initial_states(&scenario).expect("derive states");
        assert_eq!(states["A"], vec![FixedQ32::one(), FixedQ32::zero()]);
        assert_eq!(states["B"], vec![FixedQ32::neg_one(), FixedQ32::zero()]);
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
}
