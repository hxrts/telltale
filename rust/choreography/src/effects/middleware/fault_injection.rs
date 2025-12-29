// Fault injection middleware for testing
//
// Allows injecting failures and delays for chaos engineering and testing.

#[cfg(feature = "test-utils")]
use async_trait::async_trait;
#[cfg(feature = "test-utils")]
use serde::{de::DeserializeOwned, Serialize};
#[cfg(feature = "test-utils")]
use std::time::Duration;

#[cfg(feature = "test-utils")]
use crate::effects::{ChoreoHandler, Label, Result};

/// Fault injection middleware for testing
#[cfg(feature = "test-utils")]
pub struct FaultInjection<H> {
    inner: H,
    failure_rate: f32,
    delay_range: Option<(Duration, Duration)>,
    rng: rand::rngs::StdRng,
}

#[cfg(feature = "test-utils")]
impl<H> FaultInjection<H> {
    pub fn new(inner: H, failure_rate: f32) -> Self {
        use rand::SeedableRng;
        Self {
            inner,
            failure_rate,
            delay_range: None,
            rng: rand::rngs::StdRng::from_entropy(),
        }
    }

    pub fn with_delays(mut self, min: Duration, max: Duration) -> Self {
        self.delay_range = Some((min, max));
        self
    }
}

#[cfg(feature = "test-utils")]
#[async_trait]
impl<H: ChoreoHandler + Send> ChoreoHandler for FaultInjection<H> {
    type Role = H::Role;
    type Endpoint = H::Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> Result<()> {
        use rand::Rng;

        // Inject random delay
        if let Some((min, max)) = self.delay_range {
            let delay_ms = self.rng.gen_range(min.as_millis()..=max.as_millis());
            let delay = Duration::from_millis(delay_ms as u64);

            #[cfg(not(target_arch = "wasm32"))]
            {
                tokio::time::sleep(delay).await;
            }

            #[cfg(target_arch = "wasm32")]
            {
                wasm_timer::Delay::new(delay).await.ok();
            }
        }

        // Inject random failure
        if self.rng.gen::<f32>() < self.failure_rate {
            return Err(crate::effects::ChoreographyError::Transport(
                "Injected fault".into(),
            ));
        }

        self.inner.send(ep, to, msg).await
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<M> {
        self.inner.recv(ep, from).await
    }

    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: Label,
    ) -> Result<()> {
        self.inner.choose(ep, who, label).await
    }

    async fn offer(&mut self, ep: &mut Self::Endpoint, from: Self::Role) -> Result<Label> {
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
