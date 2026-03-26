// Recording effect handler for testing
//
// Captures all choreographic effects for verification and testing.
// Does not produce actual values - use for protocol structure testing only.

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::time::Duration;

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
