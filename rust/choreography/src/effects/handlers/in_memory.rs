// In-memory effect handler for testing
//
// Uses futures channels to simulate message passing between roles without
// requiring actual network communication. Ideal for protocol testing.
// WASM-compatible.

use async_trait::async_trait;
use futures::channel::mpsc::{unbounded, UnboundedReceiver, UnboundedSender};
use futures::StreamExt;
use serde::{de::DeserializeOwned, Serialize};
use std::collections::HashMap;
use std::time::Duration;

use crate::effects::{ChoreoHandler, ChoreoResult, ChoreographyError, RoleId};

type MessageChannelPair = (UnboundedSender<Vec<u8>>, UnboundedReceiver<Vec<u8>>);
type ChoiceChannelPair<L> = (UnboundedSender<L>, UnboundedReceiver<L>);
type MessageChannelMap<R> = std::sync::Arc<std::sync::Mutex<HashMap<(R, R), MessageChannelPair>>>;
type ChoiceChannelMap<R, L> =
    std::sync::Arc<std::sync::Mutex<HashMap<(R, R), ChoiceChannelPair<L>>>>;

/// In-memory handler for testing - uses tokio channels
pub struct InMemoryHandler<R: RoleId> {
    role: R,
    // Channel map for sending/receiving messages between roles
    channels: MessageChannelMap<R>,
    // Choice channel for broadcasting/receiving choice labels
    choice_channels: ChoiceChannelMap<R, R::Label>,
}

impl<R: RoleId> InMemoryHandler<R> {
    pub fn new(role: R) -> Self {
        Self {
            role,
            channels: std::sync::Arc::new(std::sync::Mutex::new(HashMap::new())),
            choice_channels: std::sync::Arc::new(std::sync::Mutex::new(HashMap::new())),
        }
    }

    /// Create a new handler with shared channels for coordinated testing
    pub fn with_channels(
        role: R,
        channels: MessageChannelMap<R>,
        choice_channels: ChoiceChannelMap<R, R::Label>,
    ) -> Self {
        Self {
            role,
            channels,
            choice_channels,
        }
    }

    /// Get or create a channel pair for communication between two roles
    fn get_or_create_channel(&self, from: R, to: R) -> UnboundedSender<Vec<u8>> {
        let mut channels = self
            .channels
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        channels
            .entry((from, to))
            .or_insert_with(unbounded)
            .0
            .clone()
    }

    /// Get receiver for a channel pair
    fn get_receiver(&self, from: R, to: R) -> Option<UnboundedReceiver<Vec<u8>>> {
        let mut channels = self
            .channels
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        channels.remove(&(from, to)).map(|(_, rx)| rx)
    }

    /// Get or create a choice channel pair for broadcasting choices
    fn get_or_create_choice_channel(&self, from: R, to: R) -> UnboundedSender<R::Label> {
        let mut channels = self
            .choice_channels
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        channels
            .entry((from, to))
            .or_insert_with(unbounded)
            .0
            .clone()
    }

    /// Get choice receiver for a channel pair
    fn get_choice_receiver(&self, from: R, to: R) -> Option<UnboundedReceiver<R::Label>> {
        let mut channels = self
            .choice_channels
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        channels.remove(&(from, to)).map(|(_, rx)| rx)
    }
}

#[async_trait]
impl<R: RoleId + 'static> ChoreoHandler for InMemoryHandler<R> {
    type Role = R;
    type Endpoint = ();

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> ChoreoResult<()> {
        // Serialize message
        let bytes =
            bincode::serialize(msg).map_err(|e| ChoreographyError::Serialization(e.to_string()))?;

        // Get or create channel for (self.role, to) and send bytes
        let sender = self.get_or_create_channel(self.role, to);
        sender.unbounded_send(bytes).map_err(|_| {
            ChoreographyError::Transport(format!(
                "Failed to send message from {:?} to {:?}",
                self.role, to
            ))
        })?;

        tracing::trace!(?to, "InMemoryHandler: send success");
        Ok(())
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<M> {
        tracing::trace!(?from, "InMemoryHandler: recv start");

        // Get the receiver for messages from 'from' to 'self.role'
        let mut receiver = self.get_receiver(from, self.role).ok_or_else(|| {
            ChoreographyError::Transport(format!("No channel from {:?} to {:?}", from, self.role))
        })?;

        // Wait for message
        let bytes = receiver.next().await.ok_or_else(|| {
            ChoreographyError::Transport("Channel closed while waiting for message".into())
        })?;

        // Put the receiver back
        {
            let mut channels = self
                .channels
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if let Some((tx, _)) = channels.remove(&(from, self.role)) {
                channels.insert((from, self.role), (tx, receiver));
            }
        }

        // Deserialize message
        let msg = bincode::deserialize(&bytes)
            .map_err(|e| ChoreographyError::Serialization(e.to_string()))?;

        tracing::trace!(?from, "InMemoryHandler: recv success");
        Ok(msg)
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        who: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        // Send choice label from self.role to who via the choice channel
        let sender = self.get_or_create_choice_channel(self.role, who);
        sender.unbounded_send(label).map_err(|_| {
            ChoreographyError::Transport(format!(
                "Failed to send choice from {:?} to {:?}",
                self.role, who
            ))
        })?;

        tracing::trace!(?who, ?label, "InMemoryHandler: sent choice");
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        tracing::trace!(?from, "InMemoryHandler: waiting for choice");

        // Get the choice receiver for choices from 'from' to 'self.role'
        let mut receiver = self.get_choice_receiver(from, self.role).ok_or_else(|| {
            ChoreographyError::Transport(format!(
                "No choice channel from {:?} to {:?}",
                from, self.role
            ))
        })?;

        // Wait for choice label
        let label = receiver.next().await.ok_or_else(|| {
            ChoreographyError::Transport("Choice channel closed while waiting for label".into())
        })?;

        // Put the receiver back
        {
            let mut channels = self
                .choice_channels
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if let Some((tx, _)) = channels.remove(&(from, self.role)) {
                channels.insert((from, self.role), (tx, receiver));
            }
        }

        tracing::trace!(?from, ?label, "InMemoryHandler: received choice");
        Ok(label)
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        at: Self::Role,
        dur: Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        if at == self.role {
            // Platform-specific timeout implementation
            #[cfg(not(target_arch = "wasm32"))]
            {
                match tokio::time::timeout(dur, body).await {
                    Ok(result) => result,
                    Err(_) => Err(ChoreographyError::Timeout(dur)),
                }
            }

            #[cfg(target_arch = "wasm32")]
            {
                // Use wasm_timer for WASM compatibility
                use futures::future::{select, Either};
                use futures::pin_mut;
                use wasm_timer::Delay;

                let timeout = Delay::new(dur);
                pin_mut!(body);
                pin_mut!(timeout);

                match select(body, timeout).await {
                    Either::Left((result, _)) => result,
                    Either::Right(_) => Err(ChoreographyError::Timeout(dur)),
                }
            }
        } else {
            body.await
        }
    }
}
