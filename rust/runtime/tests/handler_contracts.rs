//! Contract and behavioral tests for effect handlers.
#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use std::any::{Any, TypeId};
use std::collections::BTreeMap;
use std::future::pending;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use serde::{Deserialize, Serialize};
use telltale::Message;
use telltale_runtime::effects::interpreter::testing::MockHandler;
use telltale_runtime::effects::{
    interpret_extensible, validated_contract_profile, ChoreoHandler, ChoreoResult,
    ChoreographyError, DeliveryModel, DocumentedHandlerContract, ExtensibleHandler,
    ExtensionDispatchMode, ExtensionEffect, ExtensionError, ExtensionRegistry, HandlerContractTier,
    InMemoryHandler, LabelId, Metrics, NoOpHandler, Program, RecordingHandler, Retry, RoleId,
    TelltaleEndpoint, TelltaleHandler, TimeoutPolicy, Trace,
};
use telltale_runtime::effects::{ProtocolSemanticContract, RetryPolicy};
use telltale_runtime::{InterpretResult, InterpreterState, RoleName};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Alice,
    Bob,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestLabel {
    Accept,
}

impl LabelId for TestLabel {
    fn as_str(&self) -> &'static str {
        match self {
            TestLabel::Accept => "Accept",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "Accept" => Some(TestLabel::Accept),
            _ => None,
        }
    }
}

impl RoleId for TestRole {
    type Label = TestLabel;

    fn role_name(&self) -> RoleName {
        match self {
            TestRole::Alice => RoleName::from_static("Alice"),
            TestRole::Bob => RoleName::from_static("Bob"),
        }
    }
}

impl telltale::Role for TestRole {
    type Message = TestEnvelope;

    fn seal(&mut self) {}

    fn is_sealed(&self) -> bool {
        false
    }
}

#[derive(Debug)]
enum TestEnvelope {
    Payload(TestMessage),
}

impl Message<Box<dyn std::any::Any + Send>> for TestEnvelope {
    fn upcast(label: Box<dyn std::any::Any + Send>) -> Self {
        TestEnvelope::Payload(*label.downcast::<TestMessage>().unwrap())
    }

    fn downcast(self) -> Result<Box<dyn std::any::Any + Send>, Self> {
        match self {
            TestEnvelope::Payload(message) => Ok(Box::new(message)),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TestMessage {
    id: u32,
    payload: String,
}

#[derive(Clone, Debug)]
struct ContractExtension {
    value: u32,
}

impl ExtensionEffect<TestRole> for ContractExtension {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ContractExtension"
    }

    fn participating_roles(&self) -> Vec<TestRole> {
        vec![TestRole::Alice]
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

struct ContractExtensionHandler {
    registry: ExtensionRegistry<(), TestRole>,
    executed: Arc<Mutex<Vec<u32>>>,
}

impl ContractExtensionHandler {
    fn registered() -> Self {
        let executed = Arc::new(Mutex::new(Vec::new()));
        let mut registry = ExtensionRegistry::new();
        let observed = executed.clone();
        registry
            .register::<ContractExtension, _>(move |_ep, ext| {
                let observed = observed.clone();
                Box::pin(async move {
                    let extension = ext
                        .as_any()
                        .downcast_ref::<ContractExtension>()
                        .ok_or_else(|| ExtensionError::TypeMismatch {
                            expected: "ContractExtension",
                            actual: ext.type_name(),
                        })?;
                    observed.lock().unwrap().push(extension.value);
                    Ok(())
                })
            })
            .expect("register contract extension");
        Self { registry, executed }
    }

    fn unregistered() -> Self {
        Self {
            registry: ExtensionRegistry::new(),
            executed: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn executed(&self) -> Vec<u32> {
        self.executed.lock().unwrap().clone()
    }
}

#[async_trait::async_trait]
impl ExtensibleHandler for ContractExtensionHandler {
    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint, Self::Role> {
        &self.registry
    }
}

#[async_trait::async_trait]
impl ChoreoHandler for ContractExtensionHandler {
    type Role = TestRole;
    type Endpoint = ();

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _to: Self::Role,
        _msg: &M,
    ) -> ChoreoResult<()> {
        Ok(())
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> ChoreoResult<M> {
        Err(ChoreographyError::Transport("recv not implemented".into()))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        _label: TestLabel,
    ) -> ChoreoResult<()> {
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> ChoreoResult<TestLabel> {
        Ok(TestLabel::Accept)
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        body.await
    }
}

#[test]
fn documented_handler_contract_profiles_are_machine_checkable() {
    let in_memory = validated_contract_profile::<InMemoryHandler<TestRole>>().unwrap();
    assert_eq!(in_memory.tier, HandlerContractTier::FullProtocol);
    assert_eq!(
        in_memory.transport.delivery_model,
        DeliveryModel::InMemoryChannels
    );

    let noop = validated_contract_profile::<NoOpHandler<TestRole>>().unwrap();
    assert_eq!(noop.tier, HandlerContractTier::ObservationalHarness);
    assert!(!noop.semantics.can_materialize_values);

    let recording = validated_contract_profile::<RecordingHandler<TestRole>>().unwrap();
    assert_eq!(recording.tier, HandlerContractTier::ObservationalHarness);
    assert!(recording.semantics.exact_choice_label_preservation);

    let mock = validated_contract_profile::<MockHandler<TestRole>>().unwrap();
    assert_eq!(mock.transport.timeout_policy, TimeoutPolicy::PassThrough);
    assert!(mock.semantics.deterministic_for_regression);

    let telltale = validated_contract_profile::<TelltaleHandler<TestRole, TestEnvelope>>().unwrap();
    assert_eq!(telltale.tier, HandlerContractTier::FullProtocol);
    assert_eq!(
        telltale.transport.delivery_model,
        DeliveryModel::SessionBoundary
    );

    let traced = validated_contract_profile::<Trace<InMemoryHandler<TestRole>>>().unwrap();
    assert_eq!(traced.tier, HandlerContractTier::FullProtocol);

    let retried = validated_contract_profile::<Retry<InMemoryHandler<TestRole>>>().unwrap();
    assert_eq!(
        retried.transport.retry_policy,
        RetryPolicy::ExternalMiddleware
    );

    let metered = validated_contract_profile::<Metrics<InMemoryHandler<TestRole>>>().unwrap();
    assert_eq!(
        metered.semantics,
        ProtocolSemanticContract {
            typed_send_recv_roundtrip: true,
            exact_choice_label_preservation: true,
            fail_closed_transport_errors: true,
            timeouts_scoped_to_enforcing_role: true,
            deterministic_for_regression: true,
            can_materialize_values: true,
        }
    );
}

#[tokio::test]
async fn in_memory_handler_meets_documented_semantic_contract() {
    let channels = Arc::new(Mutex::new(BTreeMap::new()));
    let choice_channels = Arc::new(Mutex::new(BTreeMap::new()));

    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    let payload = TestMessage {
        id: 7,
        payload: "hello".to_string(),
    };
    alice.send(&mut (), TestRole::Bob, &payload).await.unwrap();
    let received: TestMessage = bob.recv(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(
        received, payload,
        "in-memory handler must preserve typed payloads"
    );

    alice
        .choose(&mut (), TestRole::Bob, TestLabel::Accept)
        .await
        .unwrap();
    let offered = bob.offer(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(
        offered,
        TestLabel::Accept,
        "in-memory handler must preserve exact choice labels"
    );

    let timed_out = alice
        .with_timeout(&mut (), TestRole::Alice, Duration::from_millis(5), async {
            pending::<()>().await;
            Ok::<(), ChoreographyError>(())
        })
        .await;
    assert!(
        matches!(timed_out, Err(ChoreographyError::Timeout(_))),
        "local timeout should be enforced by the handler"
    );

    let remote_timeout = tokio::time::timeout(
        Duration::from_millis(25),
        alice.with_timeout(&mut (), TestRole::Bob, Duration::from_millis(5), async {
            pending::<()>().await;
            Ok::<(), ChoreographyError>(())
        }),
    )
    .await;
    assert!(
        remote_timeout.is_err(),
        "timeouts for other roles must not be enforced locally"
    );
}

#[tokio::test]
async fn observational_harnesses_fail_closed_instead_of_fabricating_progress() {
    let mut recording = RecordingHandler::new(TestRole::Alice);
    let recv_result: Result<TestMessage, _> = recording.recv(&mut (), TestRole::Bob).await;
    assert!(
        recv_result.is_err(),
        "recording handler must not fabricate received values"
    );

    let mut noop = NoOpHandler::<TestRole>::new();
    let offer_result = noop.offer(&mut (), TestRole::Bob).await;
    assert!(
        offer_result.is_err(),
        "no-op handler must fail closed when a label would need to be synthesized"
    );

    let mut mock = MockHandler::new(TestRole::Alice);
    let scripted: TestMessage = TestMessage {
        id: 9,
        payload: "scripted".to_string(),
    };
    mock.add_response(
        telltale_runtime::effects::interpreter::testing::MockResponse::Message(
            bincode::serialize(&scripted).unwrap(),
        ),
    );
    let observed: TestMessage = mock.recv(&mut (), TestRole::Bob).await.unwrap();
    assert_eq!(
        observed, scripted,
        "mock handler values must come from the explicit script"
    );
}

#[tokio::test]
async fn extension_dispatch_contract_is_fail_closed_and_type_exact() {
    let dispatch = ExtensionRegistry::<(), TestRole>::dispatch_contract();
    assert_eq!(
        dispatch.mode,
        ExtensionDispatchMode::RegisteredOnlyTypeExact
    );
    assert!(dispatch.fail_closed_when_unregistered);
    assert!(dispatch.type_exact_before_side_effects);

    let mut registered = ContractExtensionHandler::registered();
    let mut endpoint = ();
    let program: Program<TestRole, ()> = Program::new()
        .ext(ContractExtension { value: 1 })
        .ext(ContractExtension { value: 2 })
        .ext(ContractExtension { value: 3 })
        .end();
    let result: InterpretResult<()> = interpret_extensible(&mut registered, &mut endpoint, program)
        .await
        .unwrap();
    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(
        registered.executed(),
        vec![1, 2, 3],
        "registered extension dispatch must stay deterministic and ordered"
    );
    assert_eq!(registered.registry.registered_handler_count(), 1);

    let mut unregistered = ContractExtensionHandler::unregistered();
    let failed: InterpretResult<()> = interpret_extensible(
        &mut unregistered,
        &mut (),
        Program::new().ext(ContractExtension { value: 99 }).end(),
    )
    .await
    .unwrap();
    match failed.final_state {
        InterpreterState::Failed(message) => {
            assert!(message.contains("Extension handler not registered"));
            assert!(message.contains("ContractExtension"));
        }
        other => panic!("expected fail-closed extension dispatch, got {other:?}"),
    }
    assert!(
        unregistered.executed().is_empty(),
        "unregistered extension dispatch must not mutate state before rejection"
    );
}

#[test]
fn telltale_handler_contract_documents_production_surface() {
    let profile =
        <TelltaleHandler<TestRole, TestEnvelope> as DocumentedHandlerContract>::contract_profile();
    assert_eq!(profile.tier, HandlerContractTier::FullProtocol);
    assert_eq!(
        profile.transport.delivery_model,
        DeliveryModel::SessionBoundary
    );

    let endpoint = TelltaleEndpoint::new(TestRole::Alice);
    assert_eq!(*endpoint.local_role(), TestRole::Alice);
}
