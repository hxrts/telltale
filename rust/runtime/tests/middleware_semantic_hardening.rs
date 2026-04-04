//! Semantic hardening tests for middleware composition.
#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use serde::{Deserialize, Serialize};
use std::any::{Any, TypeId};
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use telltale_runtime::effects::{
    interpret, interpret_extensible, ChoreoHandler, ChoreographyError, ExtensibleHandler,
    ExtensionEffect, ExtensionError, ExtensionRegistry, LabelId, Program, RoleId,
};
use telltale_runtime::{Metrics, Retry, RoleName, Trace};

#[cfg(feature = "test-utils")]
use telltale_runtime::effects::middleware::fault_injection::FaultInjection;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Bob,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestLabel {
    Default,
}

impl LabelId for TestLabel {
    fn as_str(&self) -> &'static str {
        "default"
    }

    fn from_str(label: &str) -> Option<Self> {
        (label == "default").then_some(Self::Default)
    }
}

impl RoleId for TestRole {
    type Label = TestLabel;

    fn role_name(&self) -> RoleName {
        match self {
            Self::Bob => RoleName::from_static("Bob"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
struct TestMessage(String);

#[derive(Clone)]
struct ScriptedSendHandler {
    outcomes: Arc<Mutex<VecDeque<Result<(), &'static str>>>>,
    attempts: Arc<Mutex<Vec<String>>>,
    successes: Arc<Mutex<Vec<String>>>,
}

#[derive(Clone, Debug)]
struct SemanticExtension {
    value: u32,
}

impl ExtensionEffect<TestRole> for SemanticExtension {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "SemanticExtension"
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect<TestRole>> {
        Box::new(self.clone())
    }
}

struct ExtensibleSendHandler {
    registry: ExtensionRegistry<(), TestRole>,
    executed: Arc<Mutex<Vec<u32>>>,
}

impl ExtensibleSendHandler {
    fn new() -> Self {
        let executed = Arc::new(Mutex::new(Vec::new()));
        let mut registry = ExtensionRegistry::new();
        let executed_values = executed.clone();
        registry
            .register::<SemanticExtension, _>(move |_ep, ext| {
                let executed_values = executed_values.clone();
                Box::pin(async move {
                    let ext = ext
                        .as_any()
                        .downcast_ref::<SemanticExtension>()
                        .ok_or_else(|| ExtensionError::TypeMismatch {
                            expected: "SemanticExtension",
                            actual: ext.type_name(),
                        })?;
                    executed_values.lock().unwrap().push(ext.value);
                    Ok(())
                })
            })
            .expect("register extension handler");
        Self { registry, executed }
    }
}

impl ScriptedSendHandler {
    fn new(outcomes: impl IntoIterator<Item = Result<(), &'static str>>) -> Self {
        Self {
            outcomes: Arc::new(Mutex::new(outcomes.into_iter().collect())),
            attempts: Arc::new(Mutex::new(Vec::new())),
            successes: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn attempts(&self) -> Vec<String> {
        self.attempts.lock().unwrap().clone()
    }

    fn successes(&self) -> Vec<String> {
        self.successes.lock().unwrap().clone()
    }
}

#[async_trait::async_trait]
impl ChoreoHandler for ScriptedSendHandler {
    type Role = TestRole;
    type Endpoint = ();

    async fn send<M: serde::Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        to: Self::Role,
        _msg: &M,
    ) -> Result<(), ChoreographyError> {
        let attempt_id = {
            let mut attempts = self.attempts.lock().unwrap();
            let attempt_id = format!("send:{}:{}", to.role_name(), attempts.len() + 1);
            attempts.push(attempt_id.clone());
            attempt_id
        };

        match self.outcomes.lock().unwrap().pop_front().unwrap_or(Ok(())) {
            Ok(()) => {
                self.successes.lock().unwrap().push(attempt_id);
                Ok(())
            }
            Err(message) => Err(ChoreographyError::Transport(message.to_string())),
        }
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> Result<M, ChoreographyError> {
        Err(ChoreographyError::Transport("recv not implemented".into()))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        _label: TestLabel,
    ) -> Result<(), ChoreographyError> {
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> Result<TestLabel, ChoreographyError> {
        Ok(TestLabel::Default)
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: Duration,
        body: F,
    ) -> Result<T, ChoreographyError>
    where
        F: std::future::Future<Output = Result<T, ChoreographyError>> + Send,
    {
        body.await
    }
}

#[async_trait::async_trait]
impl ChoreoHandler for ExtensibleSendHandler {
    type Role = TestRole;
    type Endpoint = ();

    async fn send<M: serde::Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _to: Self::Role,
        _msg: &M,
    ) -> Result<(), ChoreographyError> {
        Ok(())
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> Result<M, ChoreographyError> {
        Err(ChoreographyError::Transport("recv not implemented".into()))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        _label: TestLabel,
    ) -> Result<(), ChoreographyError> {
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> Result<TestLabel, ChoreographyError> {
        Ok(TestLabel::Default)
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: Duration,
        body: F,
    ) -> Result<T, ChoreographyError>
    where
        F: std::future::Future<Output = Result<T, ChoreographyError>> + Send,
    {
        body.await
    }
}

#[async_trait::async_trait]
impl ExtensibleHandler for ExtensibleSendHandler {
    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint, Self::Role> {
        &self.registry
    }
}

#[tokio::test]
async fn retry_middleware_keeps_retries_visible_without_duplicate_terminal_success() {
    let handler = ScriptedSendHandler::new([Err("drop-1"), Err("drop-2"), Ok(())]);
    let probe = handler.clone();
    let traced = Trace::new(handler);
    let mut retry = Retry::with_config(traced, 3, Duration::from_millis(0));
    let program = Program::<TestRole, TestMessage>::new()
        .send(TestRole::Bob, TestMessage("ping".to_string()))
        .end();

    let result = interpret(&mut retry, &mut (), program)
        .await
        .expect("retry should eventually succeed");

    assert_eq!(probe.attempts().len(), 3);
    assert_eq!(probe.successes().len(), 1);
    assert_eq!(
        result.final_state,
        telltale_runtime::InterpreterState::Completed
    );
}

#[tokio::test]
async fn middleware_order_keeps_metrics_semantics_explicit_and_deterministic() {
    let outer_metrics_inner = ScriptedSendHandler::new([Err("drop-1"), Err("drop-2"), Ok(())]);
    let mut outer_metrics = Metrics::new(Retry::with_config(
        outer_metrics_inner,
        3,
        Duration::from_millis(0),
    ));
    interpret(
        &mut outer_metrics,
        &mut (),
        Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage("ping".to_string()))
            .end(),
    )
    .await
    .expect("retry should eventually succeed");

    let inner_metrics_handler = ScriptedSendHandler::new([Err("drop-1"), Err("drop-2"), Ok(())]);
    let metrics = Metrics::new(inner_metrics_handler);
    let probe = metrics.clone();
    let mut retry_with_inner_metrics = Retry::with_config(metrics, 3, Duration::from_millis(0));
    interpret(
        &mut retry_with_inner_metrics,
        &mut (),
        Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage("ping".to_string()))
            .end(),
    )
    .await
    .expect("retry should eventually succeed");

    assert_eq!(outer_metrics.send_count(), 1);
    assert_eq!(outer_metrics.error_count(), 0);
    assert_eq!(probe.send_count(), 1);
    assert_eq!(probe.error_count(), 2);
}

#[tokio::test]
async fn extension_dispatch_survives_trace_retry_metrics_stack_without_duplication() {
    let handler = ExtensibleSendHandler::new();
    let probe = handler.executed.clone();
    let traced = Trace::new(handler);
    let retried = Retry::with_config(traced, 2, Duration::from_millis(0));
    let mut metrics = Metrics::new(retried);

    let program = Program::<TestRole, TestMessage>::new()
        .ext(SemanticExtension { value: 7 })
        .end();
    let result = interpret_extensible(&mut metrics, &mut (), program)
        .await
        .expect("extension effect should execute through middleware stack");

    assert_eq!(
        result.final_state,
        telltale_runtime::InterpreterState::Completed
    );
    assert_eq!(probe.lock().unwrap().clone(), vec![7]);
    assert_eq!(metrics.send_count(), 0);
    assert_eq!(metrics.recv_count(), 0);
    assert_eq!(metrics.error_count(), 0);
}

#[tokio::test]
async fn extension_dispatch_replays_deterministically_across_identical_runs() {
    async fn run_once() -> Vec<u32> {
        let handler = ExtensibleSendHandler::new();
        let probe = handler.executed.clone();
        let traced = Trace::new(handler);
        let mut retry = Retry::with_config(traced, 1, Duration::from_millis(0));
        interpret_extensible(
            &mut retry,
            &mut (),
            Program::<TestRole, TestMessage>::new()
                .ext(SemanticExtension { value: 11 })
                .end(),
        )
        .await
        .expect("extension effect should execute deterministically");
        let executed = probe.lock().unwrap().clone();
        executed
    }

    let first = run_once().await;
    let second = run_once().await;
    assert_eq!(first, second);
    assert_eq!(first, vec![11]);
}

#[cfg(feature = "test-utils")]
#[tokio::test]
async fn seeded_fault_injection_replays_the_same_failure_schedule() {
    async fn schedule(seed: u64) -> Vec<bool> {
        let mut handler = FaultInjection::with_seed(
            ScriptedSendHandler::new(std::iter::repeat(Ok(())).take(8)),
            0.5,
            seed,
        );
        let mut outcomes = Vec::new();
        for _ in 0..6 {
            let result = handler
                .send(&mut (), TestRole::Bob, &TestMessage("ping".to_string()))
                .await;
            outcomes.push(result.is_ok());
        }
        outcomes
    }

    let first = schedule(42).await;
    let second = schedule(42).await;
    let third = schedule(43).await;

    assert_eq!(
        first, second,
        "same seed must replay the same injected failures"
    );
    assert_ne!(
        first, third,
        "different seeds should produce a different schedule"
    );
}
