// Recording effect handler for testing
//
// Captures all choreographic effects for verification and testing.
// Does not produce actual values - use for protocol structure testing only.

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::time::Duration;

use crate::effects::contract::{
    DeliveryModel, DocumentedHandlerContract, ExtensionDispatchContract, ExtensionDispatchMode,
    HandlerContractProfile, HandlerContractTier, ProtocolSemanticContract, RetryPolicy,
    TimeoutPolicy, TransportPolicyContract,
};
use crate::effects::{ChoreoHandler, ChoreoResult, ChoreographyError, RoleId};

/// Recording handler for testing - captures all effects for verification
#[derive(Clone)]
pub struct RecordingHandler<R: RoleId> {
    pub events: std::sync::Arc<std::sync::Mutex<Vec<RecordedEvent<R>>>>,
    role: R,
}

#[derive(Debug, Clone)]
pub enum RecordedEvent<R: RoleId> {
    Send { from: R, to: R, msg_type: String },
    Recv { from: R, to: R, msg_type: String },
    Choose { at: R, label: <R as RoleId>::Label },
    Offer { from: R, to: R },
}

impl<R: RoleId> RecordingHandler<R> {
    pub fn new(role: R) -> Self {
        Self {
            events: std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
            role,
        }
    }

    pub fn events(&self) -> Vec<RecordedEvent<R>> {
        self.events
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone()
    }

    pub fn clear(&self) {
        self.events
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clear();
    }
}

impl<R: RoleId> DocumentedHandlerContract for RecordingHandler<R> {
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
                can_materialize_values: false,
            },
            transport: TransportPolicyContract {
                delivery_model: DeliveryModel::ScriptedHarness,
                retry_policy: RetryPolicy::None,
                timeout_policy: TimeoutPolicy::EnforcingRoleOnly,
            },
            extension_dispatch: ExtensionDispatchContract {
                mode: ExtensionDispatchMode::Unsupported,
                fail_closed_when_unregistered: false,
                type_exact_before_side_effects: false,
            },
            notes: vec![
                "captures exact operation order for regression use",
                "recv/offer intentionally fail closed after recording the attempted effect",
            ],
        }
    }
}

#[async_trait]
impl<R: RoleId + 'static> ChoreoHandler for RecordingHandler<R> {
    type Role = R;
    type Endpoint = ();

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        to: Self::Role,
        _msg: &M,
    ) -> ChoreoResult<()> {
        self.events
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(RecordedEvent::Send {
                from: self.role,
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
        self.events
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(RecordedEvent::Recv {
                from,
                to: self.role,
                msg_type: std::any::type_name::<M>().to_string(),
            });
        Err(ChoreographyError::Transport(
            "RecordingHandler cannot produce values".into(),
        ))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        at: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        self.events
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(RecordedEvent::Choose { at, label });
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        self.events
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(RecordedEvent::Offer {
                from,
                to: self.role,
            });
        Err(ChoreographyError::Transport(
            "RecordingHandler cannot produce labels".into(),
        ))
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
