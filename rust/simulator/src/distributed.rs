//! Distributed simulation builder using nested VMs.

use std::collections::{BTreeMap, BTreeSet};

use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::nested::NestedVMHandler;
use telltale_vm::vm::{VMConfig, VMError, VM};

/// Builder for distributed simulations with nested inner VMs.
pub struct DistributedSimBuilder {
    sites: BTreeMap<String, Vec<CodeImage>>,
    inter_site: Option<CodeImage>,
}

impl DistributedSimBuilder {
    /// Create an empty builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            sites: BTreeMap::new(),
            inter_site: None,
        }
    }

    /// Add a site with its local protocol images.
    #[must_use]
    pub fn add_site(mut self, name: impl Into<String>, protocols: Vec<CodeImage>) -> Self {
        self.sites.insert(name.into(), protocols);
        self
    }

    /// Set the inter-site routing protocol (outer VM).
    #[must_use]
    pub fn inter_site(mut self, protocol: CodeImage) -> Self {
        self.inter_site = Some(protocol);
        self
    }

    /// Build with a default no-op inner handler.
    ///
    /// # Errors
    ///
    /// Returns an error if the inter-site protocol is missing or loading fails.
    pub fn build(self, config: &VMConfig) -> Result<DistributedSimulation, String> {
        self.build_with(config, |_| Box::new(NoOpHandler))
    }

    /// Build with a per-site handler factory.
    ///
    /// # Errors
    ///
    /// Returns an error if the inter-site protocol is missing or loading fails.
    pub fn build_with<F>(
        self,
        config: &VMConfig,
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

        let mut outer_vm = VM::new(config.clone());
        outer_vm
            .load_choreography(&inter_site)
            .map_err(|e| format!("outer load error: {e}"))?;

        let mut nested = NestedVMHandler::new();

        for (site, protocols) in self.sites {
            let mut inner_vm = VM::new(config.clone());
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
        })
    }
}

impl Default for DistributedSimBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// A distributed simulation with an outer VM and nested handler.
pub struct DistributedSimulation {
    outer_vm: VM,
    handler: NestedVMHandler,
}

impl DistributedSimulation {
    /// Run the outer VM for a fixed number of rounds.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if the outer VM faults.
    pub fn run(&mut self, max_rounds: usize) -> Result<(), VMError> {
        self.outer_vm.run_concurrent(&self.handler, max_rounds, 1)
    }

    /// Access the outer VM.
    #[must_use]
    pub fn outer(&self) -> &VM {
        &self.outer_vm
    }

    /// Access the nested handler.
    #[must_use]
    pub fn handler(&self) -> &NestedVMHandler {
        &self.handler
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
    ) -> Result<Value, String> {
        Ok(Value::Unit)
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }
}
