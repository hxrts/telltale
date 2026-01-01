// Metrics collection middleware for effect handlers
//
// Tracks counts of sends, receives, and errors for monitoring and analysis.

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::time::Duration;

use crate::effects::{ChoreoHandler, Result, RoleId};

/// Metrics collection middleware
#[derive(Clone)]
pub struct Metrics<H> {
    inner: H,
    send_count: std::sync::Arc<std::sync::atomic::AtomicU64>,
    recv_count: std::sync::Arc<std::sync::atomic::AtomicU64>,
    error_count: std::sync::Arc<std::sync::atomic::AtomicU64>,
}

impl<H> Metrics<H> {
    pub fn new(inner: H) -> Self {
        Self {
            inner,
            send_count: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
            recv_count: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
            error_count: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
        }
    }

    pub fn send_count(&self) -> u64 {
        self.send_count.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn recv_count(&self) -> u64 {
        self.recv_count.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn error_count(&self) -> u64 {
        self.error_count.load(std::sync::atomic::Ordering::Relaxed)
    }
}

#[async_trait]
impl<H: ChoreoHandler + Send> ChoreoHandler for Metrics<H> {
    type Role = H::Role;
    type Endpoint = H::Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> Result<()> {
        let result = self.inner.send(ep, to, msg).await;
        if result.is_ok() {
            self.send_count
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        } else {
            self.error_count
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        result
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<M> {
        let result = self.inner.recv(ep, from).await;
        if result.is_ok() {
            self.recv_count
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        } else {
            self.error_count
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        result
    }

    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> Result<()> {
        self.inner.choose(ep, who, label).await
    }

    async fn offer(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<<Self::Role as RoleId>::Label> {
        self.inner.offer(ep, from).await
    }

    async fn with_timeout<F, T>(
        &mut self,
        ep: &mut Self::Endpoint,
        at: Self::Role,
        dur: Duration,
        body: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
    {
        self.inner.with_timeout(ep, at, dur, body).await
    }
}
