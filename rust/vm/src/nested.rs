//! Nested VM handler for distributed simulation.
//!
//! The outer VM schedules site coroutines; each site handler advances an
//! inner VM that runs site-local protocols.

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::coroutine::Value;
use crate::effect::EffectHandler;
use crate::vm::{ObsEvent, StepResult, VMError, VM};

struct SiteRunner {
    vm: Mutex<VM>,
    handler: Box<dyn EffectHandler>,
}

/// Effect handler that dispatches to inner VMs keyed by outer role name.
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

    /// Set how many inner VM rounds to advance per outer handler call.
    #[must_use]
    pub fn with_rounds_per_step(mut self, rounds: usize) -> Self {
        self.max_rounds_per_step = rounds.max(1);
        self
    }

    /// Register a site by name with its inner VM and handler.
    pub fn add_site(&mut self, name: impl Into<String>, vm: VM, handler: Box<dyn EffectHandler>) {
        self.sites.insert(
            name.into(),
            SiteRunner {
                vm: Mutex::new(vm),
                handler,
            },
        );
    }

    /// Get a copy of the inner VM trace for a site.
    ///
    /// # Panics
    ///
    /// Panics if the site VM mutex is poisoned.
    #[must_use]
    pub fn site_trace(&self, name: &str) -> Option<Vec<ObsEvent>> {
        self.sites.get(name).map(|site| {
            site.vm
                .lock()
                .expect("site vm lock poisoned")
                .trace()
                .to_vec()
        })
    }

    /// Check whether all coroutines in a site VM are terminal.
    ///
    /// # Panics
    ///
    /// Panics if the site VM mutex is poisoned.
    #[must_use]
    pub fn site_all_done(&self, name: &str) -> Option<bool> {
        self.sites
            .get(name)
            .map(|site| site.vm.lock().expect("site vm lock poisoned").all_done())
    }

    fn step_site(&self, name: &str) -> Result<(), String> {
        let site = self
            .sites
            .get(name)
            .ok_or_else(|| format!("unknown site: {name}"))?;

        let mut vm = site
            .vm
            .lock()
            .map_err(|_| "site vm lock poisoned".to_string())?;
        let handler = site.handler.as_ref();

        for _ in 0..self.max_rounds_per_step {
            match vm.step_round(handler, 1) {
                Ok(StepResult::Continue) => {}
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Err(VMError::Fault { fault, .. }) => {
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
    ) -> Result<Value, String> {
        self.step_site(role)?;
        Ok(Value::Unit)
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        self.step_site(role)
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        self.step_site(role)
    }
}
