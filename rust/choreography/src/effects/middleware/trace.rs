// Tracing middleware for effect handlers
//
// Logs all choreographic operations with timing information for debugging and monitoring.

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::time::{Duration, Instant};
use tracing::{debug, trace, warn};

use crate::effects::{ChoreoHandler, ChoreoResult, RoleId};

/// Tracing middleware that logs all choreographic operations
#[derive(Clone)]
pub struct Trace<H> {
    inner: H,
    prefix: String,
}

impl<H> Trace<H> {
    pub fn new(inner: H) -> Self {
        Self::with_prefix(inner, "choreo")
    }

    pub fn with_prefix(inner: H, prefix: impl Into<String>) -> Self {
        Self {
            inner,
            prefix: prefix.into(),
        }
    }
}

#[async_trait]
impl<H: ChoreoHandler + Send> ChoreoHandler for Trace<H> {
    type Role = H::Role;
    type Endpoint = H::Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> ChoreoResult<()> {
        let start = Instant::now();
        trace!(prefix = %self.prefix, ?to, "send: start");
        let result = self.inner.send(ep, to, msg).await;
        let duration = start.elapsed();
        match &result {
            Ok(()) => debug!(prefix = %self.prefix, ?to, ?duration, "send: success"),
            Err(e) => warn!(prefix = %self.prefix, ?to, ?duration, error = %e, "send: failed"),
        }
        result
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<M> {
        let start = Instant::now();
        trace!(prefix = %self.prefix, ?from, "recv: start");
        let result = self.inner.recv(ep, from).await;
        let duration = start.elapsed();
        match &result {
            Ok(_) => debug!(prefix = %self.prefix, ?from, ?duration, "recv: success"),
            Err(e) => warn!(prefix = %self.prefix, ?from, ?duration, error = %e, "recv: failed"),
        }
        result
    }

    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        debug!(prefix = %self.prefix, ?who, ?label, "choose");
        self.inner.choose(ep, who, label).await
    }

    async fn offer(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        trace!(prefix = %self.prefix, ?from, "offer: waiting");
        let label = self.inner.offer(ep, from).await?;
        debug!(prefix = %self.prefix, ?from, ?label, "offer: received");
        Ok(label)
    }

    async fn with_timeout<F, T>(
        &mut self,
        ep: &mut Self::Endpoint,
        at: Self::Role,
        dur: Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        debug!(prefix = %self.prefix, ?at, ?dur, "timeout: start");
        let start = Instant::now();
        let result = self.inner.with_timeout(ep, at, dur, body).await;
        let elapsed = start.elapsed();
        match &result {
            Ok(_) => debug!(prefix = %self.prefix, ?at, ?elapsed, "timeout: completed"),
            Err(e) => warn!(prefix = %self.prefix, ?at, ?elapsed, error = %e, "timeout: failed"),
        }
        result
    }
}
