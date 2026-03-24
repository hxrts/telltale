//! Nested ProtocolMachine handler for distributed simulation.
//!
//! The outer ProtocolMachine schedules site coroutines; each site handler advances an
//! inner ProtocolMachine that runs site-local protocols.

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::coroutine::Value;
use crate::effect::{EffectFailure, EffectHandler, EffectResult};
use crate::engine::{ObsEvent, ProtocolMachine, ProtocolMachineError, StepResult};

struct SiteRunner {
    vm: Mutex<ProtocolMachine>,
    handler: Box<dyn EffectHandler>,
}

/// Effect handler that dispatches to inner ProtocolMachines keyed by outer role name.
pub struct NestedVMHandler {
    sites: BTreeMap<String, SiteRunner>,
    max_rounds_per_step: usize,
}

impl NestedVMHandler {
    /// Create an empty nested handler.
    #[must_use]
    pub fn new() -> Self {
        Self {
            sites: BTreeMap::new(),
            max_rounds_per_step: 1,
        }
    }

    /// Set how many inner ProtocolMachine rounds to advance per outer handler call.
    #[must_use]
    pub fn with_rounds_per_step(mut self, rounds: usize) -> Self {
        self.max_rounds_per_step = rounds.max(1);
        self
    }

    /// Number of inner ProtocolMachine rounds attempted per outer handler call.
    #[must_use]
    pub fn rounds_per_step(&self) -> usize {
        self.max_rounds_per_step
    }

    /// Register a site by name with its inner ProtocolMachine and handler.
    pub fn add_site(
        &mut self,
        name: impl Into<String>,
        vm: ProtocolMachine,
        handler: Box<dyn EffectHandler>,
    ) {
        self.sites.insert(
            name.into(),
            SiteRunner {
                vm: Mutex::new(vm),
                handler,
            },
        );
    }

    /// Get a copy of the inner ProtocolMachine trace for a site.
    ///
    /// # Panics
    ///
    /// Panics if the site ProtocolMachine mutex is poisoned.
    #[must_use]
    pub fn site_trace(&self, name: &str) -> Option<Vec<ObsEvent>> {
        self.sites.get(name).map(|site| {
            site.vm
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .trace()
                .to_vec()
        })
    }

    /// Check whether all coroutines in a site ProtocolMachine are terminal.
    ///
    /// # Panics
    ///
    /// Panics if the site ProtocolMachine mutex is poisoned.
    #[must_use]
    pub fn site_all_done(&self, name: &str) -> Option<bool> {
        self.sites.get(name).map(|site| {
            site.vm
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .all_done()
        })
    }

    fn step_site(&self, name: &str) -> Result<(), String> {
        let site = self
            .sites
            .get(name)
            .ok_or_else(|| format!("unknown site: {name}"))?;

        let mut vm = site
            .vm
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let handler = site.handler.as_ref();

        for _ in 0..self.max_rounds_per_step {
            match vm.step_round(handler, 1) {
                Ok(StepResult::Continue) => {}
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Err(ProtocolMachineError::Fault { fault, .. }) => {
                    return Err(format!("inner vm fault: {fault}"));
                }
                Err(e) => return Err(e.to_string()),
            }
        }

        Ok(())
    }
}

impl Default for NestedVMHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl EffectHandler for NestedVMHandler {
    fn handle_send(
        &self,
        role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        match self.step_site(role) {
            Ok(()) => EffectResult::success(Value::Unit),
            Err(message) => EffectResult::failure(EffectFailure::contract_violation(message)),
        }
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
        match self.step_site(role) {
            Ok(()) => EffectResult::success(()),
            Err(message) => EffectResult::failure(EffectFailure::contract_violation(message)),
        }
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

    fn step(&self, role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        match self.step_site(role) {
            Ok(()) => EffectResult::success(()),
            Err(message) => EffectResult::failure(EffectFailure::contract_violation(message)),
        }
    }
}
