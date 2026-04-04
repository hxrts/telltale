//! Distributed simulation builder using nested ProtocolMachines.

use std::collections::{BTreeMap, BTreeSet};

use crate::scenario::{
    ResolvedTheoremProfile, TheoremAssumptionBundle, TheoremEligibility, TheoremEnvelopeProfile,
    TheoremSchedulerProfile,
};
use serde::{Deserialize, Serialize};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::runtime::runner::NestedProtocolMachineHandler;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError};

/// Explicit outer/inner execution contract for nested VM simulation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct NestedExecutionContract {
    /// Scheduler lane width for the outer protocol machine.
    pub outer_scheduler_concurrency: usize,
    /// Number of inner protocol-machine rounds attempted per outer handler callback.
    pub inner_rounds_per_step: usize,
}

/// Explicit execution-regime classification for nested distributed simulations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DistributedExecutionRegime {
    /// Nested distributed execution is currently an observed-only integration lane.
    NestedObserved,
}

/// Classification manifest for one distributed simulation instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DistributedRunManifest {
    /// Stable site names participating in the nested simulation.
    pub sites: Vec<String>,
    /// Nested execution contract used by the outer and inner machines.
    pub execution_contract: NestedExecutionContract,
    /// Execution-regime classification for this distributed lane.
    pub execution_regime: DistributedExecutionRegime,
    /// Theorem/profile classification exported for manifest consistency.
    pub theorem_profile: ResolvedTheoremProfile,
}

fn distributed_theorem_profile(contract: NestedExecutionContract) -> ResolvedTheoremProfile {
    let scheduler_profile = if contract.outer_scheduler_concurrency <= 1 {
        TheoremSchedulerProfile::CanonicalExact
    } else {
        TheoremSchedulerProfile::ThreadedEnvelope
    };

    ResolvedTheoremProfile {
        scheduler_profile,
        envelope_profile: TheoremEnvelopeProfile::None,
        assumption_bundle: TheoremAssumptionBundle::ObservedTransport,
        eligibility: TheoremEligibility::Ineligible,
        eligibility_reason: Some(
            "nested distributed execution is currently classified as observed-only and does not map to a theorem-backed scenario execution regime"
                .to_string(),
        ),
    }
}

impl Default for NestedExecutionContract {
    fn default() -> Self {
        Self {
            outer_scheduler_concurrency: 1,
            inner_rounds_per_step: 1,
        }
    }
}

/// Builder for distributed simulations with nested inner ProtocolMachines.
pub struct DistributedSimBuilder {
    sites: BTreeMap<String, Vec<CodeImage>>,
    inter_site: Option<CodeImage>,
    execution_contract: NestedExecutionContract,
}

impl DistributedSimBuilder {
    /// Create an empty builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            sites: BTreeMap::new(),
            inter_site: None,
            execution_contract: NestedExecutionContract::default(),
        }
    }

    /// Add a site with its local protocol images.
    #[must_use]
    pub fn add_site(mut self, name: impl Into<String>, protocols: Vec<CodeImage>) -> Self {
        self.sites.insert(name.into(), protocols);
        self
    }

    /// Set the inter-site routing protocol (outer ProtocolMachine).
    #[must_use]
    pub fn inter_site(mut self, protocol: CodeImage) -> Self {
        self.inter_site = Some(protocol);
        self
    }

    /// Replace the explicit nested execution contract.
    #[must_use]
    pub fn execution_contract(mut self, contract: NestedExecutionContract) -> Self {
        self.execution_contract = NestedExecutionContract {
            outer_scheduler_concurrency: contract.outer_scheduler_concurrency.max(1),
            inner_rounds_per_step: contract.inner_rounds_per_step.max(1),
        };
        self
    }

    /// Build with a default no-op inner handler.
    ///
    /// # Errors
    ///
    /// Returns an error if the inter-site protocol is missing or loading fails.
    pub fn build(self, config: &ProtocolMachineConfig) -> Result<DistributedSimulation, String> {
        self.build_with(config, |_| Box::new(NoOpHandler))
    }

    /// Build with a per-site handler factory.
    ///
    /// # Errors
    ///
    /// Returns an error if the inter-site protocol is missing or loading fails.
    pub fn build_with<F>(
        self,
        config: &ProtocolMachineConfig,
        mut handler_factory: F,
    ) -> Result<DistributedSimulation, String>
    where
        F: FnMut(&str) -> Box<dyn EffectHandler>,
    {
        let inter_site = self
            .inter_site
            .ok_or_else(|| "missing inter-site protocol".to_string())?;

        let site_names: BTreeSet<String> = self.sites.keys().cloned().collect();
        let outer_roles: BTreeSet<String> = inter_site.roles().into_iter().collect();
        if site_names != outer_roles {
            return Err(format!(
                "outer protocol roles {outer_roles:?} do not match sites {site_names:?}"
            ));
        }

        let mut outer_vm = ProtocolMachine::new(config.clone());
        outer_vm
            .load_choreography(&inter_site)
            .map_err(|e| format!("outer load error: {e}"))?;

        let mut nested = NestedProtocolMachineHandler::new()
            .with_rounds_per_step(self.execution_contract.inner_rounds_per_step);
        let mut manifest_sites = Vec::new();

        for (site, protocols) in self.sites {
            manifest_sites.push(site.clone());
            let mut inner_vm = ProtocolMachine::new(config.clone());
            for image in protocols {
                inner_vm
                    .load_choreography(&image)
                    .map_err(|e| format!("inner load error for {site}: {e}"))?;
            }
            let handler = handler_factory(&site);
            nested.add_site(site, inner_vm, handler);
        }

        Ok(DistributedSimulation {
            outer_vm,
            handler: nested,
            execution_contract: self.execution_contract,
            site_names: manifest_sites,
        })
    }
}

impl Default for DistributedSimBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// A distributed simulation with an outer ProtocolMachine and nested handler.
pub struct DistributedSimulation {
    outer_vm: ProtocolMachine,
    handler: NestedProtocolMachineHandler,
    execution_contract: NestedExecutionContract,
    site_names: Vec<String>,
}

impl DistributedSimulation {
    /// Run the outer ProtocolMachine for a fixed number of rounds.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if the outer ProtocolMachine faults.
    pub fn run(&mut self, max_rounds: usize) -> Result<(), ProtocolMachineError> {
        self.outer_vm
            .run_concurrent(
                &self.handler,
                max_rounds,
                self.execution_contract.outer_scheduler_concurrency,
            )
            .map(|_| ())
    }

    /// Access the outer ProtocolMachine.
    #[must_use]
    pub fn outer(&self) -> &ProtocolMachine {
        &self.outer_vm
    }

    /// Access the nested handler.
    #[must_use]
    pub fn handler(&self) -> &NestedProtocolMachineHandler {
        &self.handler
    }

    /// Configured nested execution contract.
    #[must_use]
    pub fn execution_contract(&self) -> NestedExecutionContract {
        self.execution_contract
    }

    /// Stable manifest describing the distributed execution lane and classification.
    #[must_use]
    pub fn manifest(&self) -> DistributedRunManifest {
        let mut sites = self.site_names.clone();
        sites.sort();
        DistributedRunManifest {
            sites,
            execution_contract: self.execution_contract,
            execution_regime: DistributedExecutionRegime::NestedObserved,
            theorem_profile: distributed_theorem_profile(self.execution_contract),
        }
    }
}

struct NoOpHandler;

impl EffectHandler for NoOpHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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
