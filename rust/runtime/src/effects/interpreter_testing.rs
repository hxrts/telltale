//! Mock handler with scripted responses for interpreter testing.

use super::{
    async_trait, ChoreoHandler, ChoreoResult, ChoreographyError, DeserializeOwned, RoleId,
    Serialize,
};
use crate::effects::contract::{
    DeliveryModel, DocumentedHandlerContract, ExtensionDispatchContract, ExtensionDispatchMode,
    HandlerContractProfile, HandlerContractTier, ProtocolSemanticContract, RetryPolicy,
    TimeoutPolicy, TransportPolicyContract,
};
use std::collections::VecDeque;

/// A mock handler that records operations and provides scripted responses
pub struct MockHandler<R: RoleId> {
    /// The role this handler represents (kept for debugging/future use)
    _role: R,
    recorded_operations: Vec<MockOperation<R>>,
    scripted_responses: VecDeque<MockResponse<<R as RoleId>::Label>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MockOperation<R: RoleId> {
    Send { to: R, msg_type: String },
    Recv { from: R },
    Choose { at: R, label: <R as RoleId>::Label },
    Offer { from: R },
}

#[derive(Debug, Clone)]
pub enum MockResponse<L> {
    Message(Vec<u8>),
    Label(L),
    Error(String),
}

impl<R: RoleId> MockHandler<R> {
    pub fn new(role: R) -> Self {
        Self {
            _role: role,
            recorded_operations: Vec::new(),
            scripted_responses: VecDeque::new(),
        }
    }

    pub fn add_response(&mut self, response: MockResponse<<R as RoleId>::Label>) {
        self.scripted_responses.push_back(response);
    }

    pub fn operations(&self) -> &[MockOperation<R>] {
        &self.recorded_operations
    }

    pub fn clear_operations(&mut self) {
        self.recorded_operations.clear();
    }
}

impl<R: RoleId> DocumentedHandlerContract for MockHandler<R> {
    fn contract_profile() -> HandlerContractProfile {
        HandlerContractProfile {
            handler_name: std::any::type_name::<Self>(),
            tier: HandlerContractTier::ObservationalHarness,
            semantics: ProtocolSemanticContract {
                typed_send_recv_roundtrip: false,
                exact_choice_label_preservation: true,
                fail_closed_transport_errors: true,
                timeouts_scoped_to_enforcing_role: true,
                deterministic_for_regression: true,
                can_materialize_values: true,
            },
            transport: TransportPolicyContract {
                delivery_model: DeliveryModel::ScriptedHarness,
                retry_policy: RetryPolicy::None,
                timeout_policy: TimeoutPolicy::PassThrough,
            },
            extension_dispatch: ExtensionDispatchContract {
                mode: ExtensionDispatchMode::Unsupported,
                fail_closed_when_unregistered: false,
                type_exact_before_side_effects: false,
            },
            notes: vec![
                "values and labels come only from an explicit scripted response queue",
                "missing scripted responses fail closed instead of synthesizing protocol progress",
            ],
        }
    }
}

#[async_trait]
impl<R: RoleId + 'static> ChoreoHandler for MockHandler<R> {
    type Role = R;
    type Endpoint = ();

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        to: Self::Role,
        _msg: &M,
    ) -> ChoreoResult<()> {
        self.recorded_operations.push(MockOperation::Send {
            to,
            msg_type: std::any::type_name::<M>().to_string(),
        });
        Ok(())
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<M> {
        self.recorded_operations.push(MockOperation::Recv { from });

        if let Some(MockResponse::Message(bytes)) = self.scripted_responses.pop_front() {
            bincode::deserialize(&bytes)
                .map_err(|e| ChoreographyError::Serialization(e.to_string()))
        } else {
            Err(ChoreographyError::Transport(
                "No scripted response available".into(),
            ))
        }
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        at: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        self.recorded_operations
            .push(MockOperation::Choose { at, label });
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        self.recorded_operations.push(MockOperation::Offer { from });

        if let Some(MockResponse::Label(label)) = self.scripted_responses.pop_front() {
            Ok(label)
        } else {
            Err(ChoreographyError::Transport(
                "No scripted label available".into(),
            ))
        }
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: std::time::Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        body.await
    }
}
