// Retry middleware for effect handlers
//
// Implements exponential backoff retry logic for failed send operations.

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::time::Duration;
use tracing::debug;

use crate::effects::{ChoreoHandler, Result, RoleId};

/// Retry middleware with exponential backoff
#[derive(Clone)]
pub struct Retry<H> {
    inner: H,
    max_retries: usize,
    base_delay: Duration,
}

impl<H> Retry<H> {
    pub fn new(inner: H) -> Self {
        Self {
            inner,
            max_retries: 3,
            base_delay: Duration::from_millis(100),
        }
    }

    pub fn with_config(inner: H, max_retries: usize, base_delay: Duration) -> Self {
        Self {
            inner,
            max_retries,
            base_delay,
        }
    }
}

#[async_trait]
impl<H: ChoreoHandler + Send> ChoreoHandler for Retry<H> {
    type Role = H::Role;
    type Endpoint = H::Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> Result<()> {
        let mut retries = 0;
        loop {
            match self.inner.send(ep, to, msg).await {
                Ok(()) => return Ok(()),
                Err(_e) if retries < self.max_retries => {
                    retries += 1;
                    let delay = self.base_delay * (1 << (retries - 1));
                    debug!(?to, ?retries, ?delay, "send failed, retrying");
                    // Platform-specific sleep
                    #[cfg(not(target_arch = "wasm32"))]
                    {
                        tokio::time::sleep(delay).await;
                    }

                    #[cfg(target_arch = "wasm32")]
                    {
                        wasm_timer::Delay::new(delay).await.ok();
                    }
                }
                Err(e) => return Err(e),
            }
        }
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<M> {
        // Recv typically shouldn't be retried as it changes protocol state
        self.inner.recv(ep, from).await
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
