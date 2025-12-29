#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Complete workflow example with multiple extension types
//!
//! This example demonstrates a realistic authentication workflow using:
//! - Capability validation
//! - Flow cost tracking
//! - Logging
//! - Metrics collection

use rumpsteak_aura_choreography::effects::*;
use std::any::{Any, TypeId};
use std::sync::{Arc, Mutex};

// ============================================================================
// Domain Types
// ============================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Role {
    Client,
    Server,
    Database,
}

// ============================================================================
// Extension Definitions
// ============================================================================

#[derive(Clone, Debug)]
struct ValidateCapability {
    capability: String,
    role: Role,
}

impl ExtensionEffect for ValidateCapability {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ValidateCapability"
    }

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![Box::new(self.role)]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
struct ChargeFlowCost {
    cost: u32,
    role: Role,
}

impl ExtensionEffect for ChargeFlowCost {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ChargeFlowCost"
    }

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![Box::new(self.role)]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
struct LogEvent {
    message: String,
    level: LogLevel,
}

#[derive(Clone, Debug)]
enum LogLevel {
    Info,
    Warn,
    Error,
}

impl ExtensionEffect for LogEvent {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "LogEvent"
    }

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![] // Global
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
struct RecordMetric {
    metric: String,
    value: u64,
}

impl ExtensionEffect for RecordMetric {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "RecordMetric"
    }

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        vec![]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect> {
        Box::new(self.clone())
    }
}

// ============================================================================
// Extensible Handler
// ============================================================================

struct WorkflowHandler {
    role: Role,
    registry: ExtensionRegistry<()>,
    budget: Arc<Mutex<u32>>,
    metrics: Arc<Mutex<Vec<(String, u64)>>>,
}

impl WorkflowHandler {
    fn new(role: Role, capabilities: Vec<String>, initial_budget: u32) -> Self {
        let budget = Arc::new(Mutex::new(initial_budget));
        let metrics = Arc::new(Mutex::new(Vec::new()));
        let mut registry = ExtensionRegistry::new();

        // Register capability validation
        let caps = capabilities.clone();
        registry.register::<ValidateCapability, _>(move |_ep, ext| {
            let caps = caps.clone();
            Box::pin(async move {
                let validate = ext.as_any().downcast_ref::<ValidateCapability>().ok_or(
                    ExtensionError::TypeMismatch {
                        expected: "ValidateCapability",
                        actual: ext.type_name(),
                    },
                )?;

                if !caps.contains(&validate.capability) {
                    return Err(ExtensionError::ExecutionFailed {
                        type_name: "ValidateCapability",
                        error: format!("Missing capability: {}", validate.capability),
                    });
                }

                println!(
                    "[{:?}] Validated capability: {}",
                    validate.role, validate.capability
                );
                Ok(())
            })
        });

        // Register flow cost tracking
        let budget_ref = budget.clone();
        registry.register::<ChargeFlowCost, _>(move |_ep, ext| {
            let budget = budget_ref.clone();
            Box::pin(async move {
                let cost = ext.as_any().downcast_ref::<ChargeFlowCost>().ok_or(
                    ExtensionError::TypeMismatch {
                        expected: "ChargeFlowCost",
                        actual: ext.type_name(),
                    },
                )?;

                let mut budget_lock = budget.lock().unwrap();
                if *budget_lock < cost.cost {
                    return Err(ExtensionError::ExecutionFailed {
                        type_name: "ChargeFlowCost",
                        error: format!("Insufficient budget: {} < {}", *budget_lock, cost.cost),
                    });
                }

                *budget_lock -= cost.cost;
                println!(
                    "[{:?}] Charged {} units (remaining: {})",
                    cost.role, cost.cost, *budget_lock
                );
                Ok(())
            })
        });

        // Register logging
        registry.register::<LogEvent, _>(|_ep, ext| {
            Box::pin(async move {
                let log = ext.as_any().downcast_ref::<LogEvent>().ok_or(
                    ExtensionError::TypeMismatch {
                        expected: "LogEvent",
                        actual: ext.type_name(),
                    },
                )?;

                match log.level {
                    LogLevel::Info => println!("[INFO] {}", log.message),
                    LogLevel::Warn => println!("[WARN] {}", log.message),
                    LogLevel::Error => println!("[ERROR] {}", log.message),
                }
                Ok(())
            })
        });

        // Register metrics
        let metrics_ref = metrics.clone();
        registry.register::<RecordMetric, _>(move |_ep, ext| {
            let metrics = metrics_ref.clone();
            Box::pin(async move {
                let metric = ext.as_any().downcast_ref::<RecordMetric>().ok_or(
                    ExtensionError::TypeMismatch {
                        expected: "RecordMetric",
                        actual: ext.type_name(),
                    },
                )?;

                metrics
                    .lock()
                    .unwrap()
                    .push((metric.metric.clone(), metric.value));
                println!("Metric: {} = {}", metric.metric, metric.value);
                Ok(())
            })
        });

        Self {
            role,
            registry,
            budget,
            metrics,
        }
    }

    fn remaining_budget(&self) -> u32 {
        *self.budget.lock().unwrap()
    }

    fn collected_metrics(&self) -> Vec<(String, u64)> {
        self.metrics.lock().unwrap().clone()
    }
}

#[async_trait::async_trait]
impl ExtensibleHandler for WorkflowHandler {
    type Endpoint = ();

    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint> {
        &self.registry
    }
}

#[async_trait::async_trait]
impl ChoreoHandler for WorkflowHandler {
    type Role = Role;
    type Endpoint = ();

    async fn send<M: serde::Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        to: Self::Role,
        _msg: &M,
    ) -> Result<()> {
        println!("[{:?}] -> [{:?}] Message sent", self.role, to);
        Ok(())
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<M> {
        println!("[{:?}] <- [{:?}] Message received", self.role, from);
        Err(ChoreographyError::Transport(
            "recv not implemented in example".into(),
        ))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        label: Label,
    ) -> Result<()> {
        println!("[{:?}] Choice: {}", self.role, label.0);
        Ok(())
    }

    async fn offer(&mut self, _ep: &mut Self::Endpoint, from: Self::Role) -> Result<Label> {
        println!("[{:?}] Offering choice from {:?}", self.role, from);
        Ok(Label("default"))
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: std::time::Duration,
        body: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
    {
        body.await
    }
}

// ============================================================================
// Choreography Definition
// ============================================================================

// Helper to demonstrate all log levels
fn _example_log_levels() -> Program<Role, String> {
    Program::new()
        .ext(LogEvent {
            message: "This is an info message".into(),
            level: LogLevel::Info,
        })
        .ext(LogEvent {
            message: "This is a warning message".into(),
            level: LogLevel::Warn,
        })
        .ext(LogEvent {
            message: "This is an error message".into(),
            level: LogLevel::Error,
        })
        .end()
}

fn authentication_workflow() -> Program<Role, String> {
    Program::new()
        // Protocol start
        .ext(LogEvent {
            message: "Authentication workflow started".into(),
            level: LogLevel::Info,
        })
        .ext(RecordMetric {
            metric: "auth_started".into(),
            value: 1,
        })
        // Client validates capability and pays for request
        .ext(ValidateCapability {
            capability: "authenticate".into(),
            role: Role::Client,
        })
        .ext(ChargeFlowCost {
            cost: 100,
            role: Role::Client,
        })
        .ext(LogEvent {
            message: "High cost operation - check budget".into(),
            level: LogLevel::Warn,
        })
        .send(Role::Server, "auth_request".into())
        // Server validates and queries database
        .ext(LogEvent {
            message: "Server processing authentication".into(),
            level: LogLevel::Info,
        })
        .ext(ValidateCapability {
            capability: "query_users".into(),
            role: Role::Server,
        })
        .ext(ChargeFlowCost {
            cost: 50,
            role: Role::Server,
        })
        .send(Role::Database, "user_query".into())
        // Database processes query
        .ext(ValidateCapability {
            capability: "read_users".into(),
            role: Role::Database,
        })
        .ext(ChargeFlowCost {
            cost: 25,
            role: Role::Database,
        })
        .ext(LogEvent {
            message: "Database query cost exceeds threshold".into(),
            level: LogLevel::Error,
        })
        .send(Role::Server, "user_data".into())
        // Server sends response to client
        .ext(ChargeFlowCost {
            cost: 30,
            role: Role::Server,
        })
        .send(Role::Client, "auth_response".into())
        // Protocol completion
        .ext(LogEvent {
            message: "Authentication successful".into(),
            level: LogLevel::Info,
        })
        .ext(RecordMetric {
            metric: "auth_success".into(),
            value: 1,
        })
        .end()
}

// ============================================================================
// Main
// ============================================================================

#[tokio::main]
async fn main() {
    println!("{}", "=".repeat(60));
    println!("Extension Workflow Example: Authentication Protocol");
    println!("{}", "=".repeat(60));
    println!();

    // Create handler with capabilities and budget
    let mut handler = WorkflowHandler::new(
        Role::Client,
        vec![
            "authenticate".into(),
            "query_users".into(),
            "read_users".into(),
        ],
        500, // Initial budget
    );

    println!("Initial budget: {} units\n", handler.remaining_budget());

    // Build choreography
    let program = authentication_workflow();
    println!("Program has {} effects\n", program.len());

    // Execute with extensions
    let mut endpoint = ();
    match interpret_extensible(&mut handler, &mut endpoint, program).await {
        Ok(result) => {
            println!();
            println!("{}", "=".repeat(60));
            match result.final_state {
                InterpreterState::Completed => {
                    println!("Protocol completed successfully");
                }
                InterpreterState::Failed(err) => {
                    println!("Protocol failed: {}", err);
                }
                InterpreterState::Timeout => {
                    println!("Protocol timed out");
                }
            }

            println!();
            println!("Final budget: {} units", handler.remaining_budget());
            println!();
            println!("Collected metrics:");
            for (metric, value) in handler.collected_metrics() {
                println!("  {} = {}", metric, value);
            }
            println!("{}", "=".repeat(60));
        }
        Err(e) => {
            println!("\nError: {}", e);
        }
    }
}
