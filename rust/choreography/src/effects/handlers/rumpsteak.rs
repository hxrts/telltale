// Rumpsteak session-typed effect handler
//
// This handler provides a unified abstraction over bidirectional channels
// and dynamically dispatched session objects. Users can keep using the
// legacy SimpleChannel transport or register custom session interpreters
// through the RumpsteakSession wrapper.
//
// Key pieces:
// - SimpleChannel: thin wrapper around rumpsteak bidirectional channels.
// - SessionTypeDynamic: async trait (object safe via BoxFuture) that lets any
//   session state expose send/recv/choose/offer operations.
// - RumpsteakSession: boxed dynamic session with metadata integration.
// - RumpsteakEndpoint: tracks per-peer channels/sessions plus metadata.
// - RumpsteakHandler: implements ChoreoHandler over either transport.

use async_trait::async_trait;
use futures::{channel::mpsc, future::BoxFuture, SinkExt, StreamExt};
use serde::{de::DeserializeOwned, Serialize};
use std::{collections::HashMap, fmt::Debug, marker::PhantomData, time::Duration};

use crate::effects::{ChoreoHandler, ChoreographyError, Label, Result, RoleId};
use rumpsteak_aura::{
    channel::{Bidirectional, Pair},
    Message, Role,
};

/// Metadata describing the evolution of a session with a peer.
#[derive(Debug, Clone)]
pub struct SessionMetadata {
    /// Human-readable description of the last state/operation.
    pub state_description: String,
    /// Whether the session has reached its terminal state.
    pub is_complete: bool,
    /// Number of operations performed on this session.
    pub operation_count: usize,
}

impl Default for SessionMetadata {
    fn default() -> Self {
        Self {
            state_description: "Initial".to_string(),
            is_complete: false,
            operation_count: 0,
        }
    }
}

/// Simple bidirectional channel used for backward compatibility.
type SimpleChannelInner =
    Bidirectional<mpsc::UnboundedSender<Vec<u8>>, mpsc::UnboundedReceiver<Vec<u8>>>;
#[derive(Debug)]
pub struct SimpleChannel {
    inner: SimpleChannelInner,
}

impl SimpleChannel {
    /// Create a pair of connected channels.
    #[must_use]
    pub fn pair() -> (Self, Self) {
        let (left, right) = SimpleChannelInner::pair();
        (Self { inner: left }, Self { inner: right })
    }

    /// Send raw bytes across the channel.
    pub async fn send(&mut self, msg: Vec<u8>) -> std::result::Result<(), String> {
        self.inner
            .send(msg)
            .await
            .map_err(|e| format!("Send failed: {e}"))
    }

    /// Receive raw bytes from the channel.
    pub async fn recv(&mut self) -> std::result::Result<Vec<u8>, String> {
        self.inner
            .next()
            .await
            .ok_or_else(|| "Channel closed".to_string())
    }
}

/// Result of executing a session operation.
#[derive(Debug)]
pub struct SessionUpdate<T> {
    pub output: T,
    pub description: Option<String>,
    pub is_complete: bool,
}

impl<T> SessionUpdate<T> {
    pub fn new(output: T) -> Self {
        Self {
            output,
            description: None,
            is_complete: false,
        }
    }

    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }

    pub fn mark_complete(mut self) -> Self {
        self.is_complete = true;
        self
    }
}

/// Dynamic session trait used by `RumpsteakSession`.
pub trait SessionTypeDynamic: Send {
    /// Identify the underlying session for diagnostics.
    fn type_name(&self) -> &'static str;

    /// Send a serialized message.
    fn send(&mut self, _data: Vec<u8>) -> BoxFuture<'_, Result<SessionUpdate<()>>> {
        unsupported("send", self.type_name())
    }

    /// Receive a serialized message.
    fn recv(&mut self) -> BoxFuture<'_, Result<SessionUpdate<Vec<u8>>>> {
        unsupported("recv", self.type_name())
    }

    /// Make a choice/selection.
    fn choose(&mut self, _label: &str) -> BoxFuture<'_, Result<SessionUpdate<()>>> {
        unsupported("choose", self.type_name())
    }

    /// Offer a branch selection.
    fn offer(&mut self) -> BoxFuture<'_, Result<SessionUpdate<String>>> {
        unsupported("offer", self.type_name())
    }
}

fn unsupported<T>(
    operation: &'static str,
    name: &'static str,
) -> BoxFuture<'static, Result<SessionUpdate<T>>> {
    Box::pin(async move {
        Err(ChoreographyError::ProtocolViolation(format!(
            "{name} does not support {operation} operations"
        )))
    })
}

/// Generic session backed by independent sink/stream pairs.
struct SinkStreamSession<S, R> {
    sender: S,
    receiver: R,
    label: &'static str,
}

impl<S, R> SinkStreamSession<S, R> {
    fn new(sender: S, receiver: R, label: &'static str) -> Self {
        Self {
            sender,
            receiver,
            label,
        }
    }
}

impl<S, R> SessionTypeDynamic for SinkStreamSession<S, R>
where
    S: futures::Sink<Vec<u8>> + Unpin + Send,
    S::Error: std::fmt::Display + Send + 'static,
    R: futures::Stream<Item = Vec<u8>> + Unpin + Send,
{
    fn type_name(&self) -> &'static str {
        self.label
    }

    fn send(&mut self, data: Vec<u8>) -> BoxFuture<'_, Result<SessionUpdate<()>>> {
        let sender = &mut self.sender;
        Box::pin(async move {
            sender
                .send(data)
                .await
                .map_err(|e| ChoreographyError::Transport(format!("Channel send failed: {e}")))?;
            Ok(SessionUpdate::new(()).with_description("Send"))
        })
    }

    fn recv(&mut self) -> BoxFuture<'_, Result<SessionUpdate<Vec<u8>>>> {
        let receiver = &mut self.receiver;
        Box::pin(async move {
            let bytes = receiver.next().await.ok_or_else(|| {
                ChoreographyError::Transport("Channel closed while receiving".into())
            })?;
            Ok(SessionUpdate::new(bytes).with_description("Recv"))
        })
    }

    fn choose(&mut self, label: &str) -> BoxFuture<'_, Result<SessionUpdate<()>>> {
        let sender = &mut self.sender;
        let data = label.to_string();
        Box::pin(async move {
            let bytes = bincode::serialize(&data).map_err(|e| {
                ChoreographyError::Transport(format!("Label serialization failed: {e}"))
            })?;
            sender
                .send(bytes)
                .await
                .map_err(|e| ChoreographyError::Transport(format!("Channel send failed: {e}")))?;
            Ok(SessionUpdate::new(()).with_description("Choose"))
        })
    }

    fn offer(&mut self) -> BoxFuture<'_, Result<SessionUpdate<String>>> {
        let receiver = &mut self.receiver;
        Box::pin(async move {
            let bytes = receiver.next().await.ok_or_else(|| {
                ChoreographyError::Transport("Channel closed while waiting for choice".into())
            })?;
            let label: String = bincode::deserialize(&bytes).map_err(|e| {
                ChoreographyError::Transport(format!("Label deserialization failed: {e}"))
            })?;
            Ok(SessionUpdate::new(label).with_description("Offer"))
        })
    }
}

/// `SimpleSession` reuses `SimpleChannel` but routes operations through the
/// dynamic trait so that session-typed channels and legacy transport share
/// the same machinery.
struct SimpleSession {
    channel: SimpleChannel,
}

impl SimpleSession {
    fn new(channel: SimpleChannel) -> Self {
        Self { channel }
    }
}

impl SessionTypeDynamic for SimpleSession {
    fn type_name(&self) -> &'static str {
        "SimpleSession"
    }

    fn send(&mut self, data: Vec<u8>) -> BoxFuture<'_, Result<SessionUpdate<()>>> {
        let channel = &mut self.channel;
        Box::pin(async move {
            channel.send(data).await.map_err(|e| {
                ChoreographyError::Transport(format!("SimpleSession send failed: {e}"))
            })?;
            Ok(SessionUpdate::new(()).with_description("Send"))
        })
    }

    fn recv(&mut self) -> BoxFuture<'_, Result<SessionUpdate<Vec<u8>>>> {
        let channel = &mut self.channel;
        Box::pin(async move {
            let bytes = channel.recv().await.map_err(|e| {
                ChoreographyError::Transport(format!("SimpleSession recv failed: {e}"))
            })?;
            Ok(SessionUpdate::new(bytes).with_description("Recv"))
        })
    }

    fn choose(&mut self, label: &str) -> BoxFuture<'_, Result<SessionUpdate<()>>> {
        let channel = &mut self.channel;
        let label = label.to_string();
        Box::pin(async move {
            let bytes = bincode::serialize(&label).map_err(|e| {
                ChoreographyError::Transport(format!("Label serialization failed: {e}"))
            })?;
            channel.send(bytes).await.map_err(|e| {
                ChoreographyError::Transport(format!("SimpleSession choose failed: {e}"))
            })?;
            Ok(SessionUpdate::new(()).with_description("Choose"))
        })
    }

    fn offer(&mut self) -> BoxFuture<'_, Result<SessionUpdate<String>>> {
        let channel = &mut self.channel;
        Box::pin(async move {
            let bytes = channel.recv().await.map_err(|e| {
                ChoreographyError::Transport(format!("SimpleSession offer failed: {e}"))
            })?;
            let label: String = bincode::deserialize(&bytes).map_err(|e| {
                ChoreographyError::Transport(format!("Label deserialization failed: {e}"))
            })?;
            Ok(SessionUpdate::new(label).with_description("Offer"))
        })
    }
}

/// Wrapper around a dynamic session object.
pub struct RumpsteakSession {
    inner: Box<dyn SessionTypeDynamic>,
}

impl Debug for RumpsteakSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RumpsteakSession")
            .field("session", &self.type_name())
            .finish()
    }
}

impl RumpsteakSession {
    #[must_use]
    pub fn new(inner: Box<dyn SessionTypeDynamic>) -> Self {
        Self { inner }
    }

    #[must_use]
    pub fn from_simple_channel(channel: SimpleChannel) -> Self {
        Self::new(Box::new(SimpleSession::new(channel)))
    }

    /// Build a session from independent sink/stream transports.
    pub fn from_sink_stream<S, R>(sender: S, receiver: R) -> Self
    where
        S: futures::Sink<Vec<u8>> + Unpin + Send + 'static,
        S::Error: std::fmt::Display + Send + 'static,
        R: futures::Stream<Item = Vec<u8>> + Unpin + Send + 'static,
    {
        let label = std::any::type_name::<S>();
        Self::new(Box::new(SinkStreamSession::new(sender, receiver, label)))
    }

    #[must_use]
    pub fn type_name(&self) -> &'static str {
        self.inner.type_name()
    }

    pub async fn send(&mut self, data: Vec<u8>) -> Result<SessionUpdate<()>> {
        self.inner.send(data).await
    }

    pub async fn recv(&mut self) -> Result<SessionUpdate<Vec<u8>>> {
        self.inner.recv().await
    }

    pub async fn choose(&mut self, label: &str) -> Result<SessionUpdate<()>> {
        self.inner.choose(label).await
    }

    pub async fn offer(&mut self) -> Result<SessionUpdate<String>> {
        self.inner.offer().await
    }
}

enum ChannelState {
    Simple(SimpleChannel),
    Session(RumpsteakSession),
}

struct ChannelRecord {
    state: ChannelState,
    metadata: SessionMetadata,
}

/// Endpoint that manages per-peer channels/sessions plus metadata.
pub struct RumpsteakEndpoint<R>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    local_role: R,
    channels: HashMap<R, ChannelRecord>,
}

impl<R> RumpsteakEndpoint<R>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    pub fn new(local_role: R) -> Self {
        Self {
            local_role,
            channels: HashMap::new(),
        }
    }

    /// Register a legacy `SimpleChannel` for a peer.
    pub fn register_channel(&mut self, peer: R, channel: SimpleChannel) {
        tracing::debug!(?peer, "Registering SimpleChannel session");
        self.channels.insert(
            peer,
            ChannelRecord {
                state: ChannelState::Simple(channel),
                metadata: SessionMetadata::default(),
            },
        );
    }

    /// Register a dynamic session for a peer.
    pub fn register_session(&mut self, peer: R, session: RumpsteakSession) {
        tracing::debug!(peer = ?peer, session = session.type_name(), "Registering dynamic session");
        self.channels.insert(
            peer,
            ChannelRecord {
                state: ChannelState::Session(session),
                metadata: SessionMetadata::default(),
            },
        );
    }

    fn take_record(&mut self, peer: &R) -> Option<ChannelRecord> {
        self.channels.remove(peer)
    }

    fn put_record(&mut self, peer: R, record: ChannelRecord) {
        self.channels.insert(peer, record);
    }

    pub fn has_channel(&self, peer: &R) -> bool {
        self.channels.contains_key(peer)
    }

    pub fn close_channel(&mut self, peer: &R) -> bool {
        self.channels.remove(peer).is_some()
    }

    pub fn close_all_channels(&mut self) -> usize {
        let count = self.channels.len();
        self.channels.clear();
        count
    }

    pub fn is_all_closed(&self) -> bool {
        self.channels.is_empty()
    }

    pub fn active_channel_count(&self) -> usize {
        self.channels.len()
    }

    pub fn local_role(&self) -> &R {
        &self.local_role
    }

    pub fn get_metadata(&self, peer: &R) -> Option<&SessionMetadata> {
        self.channels.get(peer).map(|record| &record.metadata)
    }

    pub fn all_metadata(&self) -> Vec<(R, &SessionMetadata)> {
        self.channels
            .iter()
            .map(|(peer, record)| (peer.clone(), &record.metadata))
            .collect()
    }
}

impl<R> Drop for RumpsteakEndpoint<R>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    fn drop(&mut self) {
        let active = self.active_channel_count();
        if active > 0 {
            tracing::warn!(active, "Endpoint dropped with active channels; closing");
            self.close_all_channels();
        }
    }
}

/// Effect handler backed by Rumpsteak sessions.
pub struct RumpsteakHandler<R, M> {
    _phantom: PhantomData<(R, M)>,
}

impl<R, M> RumpsteakHandler<R, M>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    async fn with_channel_operation<T, F, Fut>(
        ep: &mut RumpsteakEndpoint<R>,
        peer: &R,
        default_description: &str,
        f: F,
    ) -> Result<T>
    where
        F: FnOnce(ChannelState) -> Fut,
        Fut: std::future::Future<Output = Result<(T, ChannelState, Option<String>, bool)>>,
    {
        let mut record = ep.take_record(peer).ok_or_else(|| {
            ChoreographyError::Transport(format!("No channel registered for peer: {peer:?}"))
        })?;

        let (result, next_state, description, completed) = f(record.state).await?;
        record.state = next_state;
        record.metadata.operation_count += 1;
        record.metadata.state_description =
            description.unwrap_or_else(|| default_description.to_string());
        if completed {
            record.metadata.is_complete = true;
        }

        ep.put_record(peer.clone(), record);
        Ok(result)
    }
}

impl<R, M> Default for RumpsteakHandler<R, M>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl<R, M> ChoreoHandler for RumpsteakHandler<R, M>
where
    R: Role<Message = M> + Send + Sync + RoleId + Eq + std::hash::Hash + Clone + Debug + 'static,
    M: Message<Box<dyn std::any::Any + Send>> + Send + Sync + 'static,
{
    type Role = R;
    type Endpoint = RumpsteakEndpoint<R>;

    async fn send<Msg: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &Msg,
    ) -> Result<()> {
        let serialized = bincode::serialize(msg)
            .map_err(|e| ChoreographyError::Transport(format!("Serialization failed: {e}")))?;

        Self::with_channel_operation(ep, &to, "Send", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    channel.send(serialized).await.map_err(|e| {
                        ChoreographyError::Transport(format!("SimpleChannel send failed: {e}"))
                    })?;
                    Ok(((), ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.send(serialized).await?;
                    Ok((
                        (),
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn recv<Msg: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<Msg> {
        Self::with_channel_operation(ep, &from, "Recv", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    let serialized = channel.recv().await.map_err(|e| {
                        ChoreographyError::Transport(format!("SimpleChannel recv failed: {e}"))
                    })?;
                    let msg = bincode::deserialize(&serialized).map_err(|e| {
                        ChoreographyError::Transport(format!("Deserialization failed: {e}"))
                    })?;
                    Ok((msg, ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.recv().await?;
                    let msg = bincode::deserialize(&update.output).map_err(|e| {
                        ChoreographyError::Transport(format!("Deserialization failed: {e}"))
                    })?;
                    Ok((
                        msg,
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: Label,
    ) -> Result<()> {
        let label_str = label.0.to_string();
        Self::with_channel_operation(ep, &who, "Choose", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    let serialized = bincode::serialize(&label_str).map_err(|e| {
                        ChoreographyError::Transport(format!("Label serialization failed: {e}"))
                    })?;
                    channel.send(serialized).await.map_err(|e| {
                        ChoreographyError::Transport(format!("Choice send failed: {e}"))
                    })?;
                    Ok(((), ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.choose(&label_str).await?;
                    Ok((
                        (),
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn offer(&mut self, ep: &mut Self::Endpoint, from: Self::Role) -> Result<Label> {
        Self::with_channel_operation(ep, &from, "Offer", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    let serialized = channel.recv().await.map_err(|e| {
                        ChoreographyError::Transport(format!("Choice receive failed: {e}"))
                    })?;
                    let label_string: String = bincode::deserialize(&serialized).map_err(|e| {
                        ChoreographyError::Transport(format!("Label deserialization failed: {e}"))
                    })?;
                    let leaked: &'static str = Box::leak(label_string.into_boxed_str());
                    Ok((Label(leaked), ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.offer().await?;
                    let leaked: &'static str = Box::leak(update.output.into_boxed_str());
                    Ok((
                        Label(leaked),
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        dur: Duration,
        body: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
    {
        #[cfg(not(target_arch = "wasm32"))]
        {
            match tokio::time::timeout(dur, body).await {
                Ok(result) => result,
                Err(_) => Err(ChoreographyError::Timeout(dur)),
            }
        }

        #[cfg(target_arch = "wasm32")]
        {
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
    }
}
